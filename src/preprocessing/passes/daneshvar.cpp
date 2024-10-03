    /******************************************************************************
 * Top contributors (to current version):
 *   Daneshvar Amrollahi
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The strings eager preprocess utility.
 */

#include "preprocessing/passes/daneshvar.h"

#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/sort_to_term.h"
#include "util/string.h"
#include "expr/node_converter.h"
#include "util/statistics_registry.h"
#include "preprocessing/preprocessing_pass_context.h" 

#include <map>
#include <unordered_map>
#include <memory>
#include <tuple>
#include <stack>

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;


namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Daneshvar::Daneshvar(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "daneshvar"),
    d_statistics(statisticsRegistry())
    {};


void generateEncoding(
    const Node& root,
    std::string& encoding,
    std::map<std::string, int32_t>& role)
{
    std::stack<Node> stack;
    std::unordered_map<Node, bool> visited;           // Map to keep track of visited nodes
    std::unordered_map<Node, uint32_t> subtreeIdMap;  // Map from Nodes to their IDs
    std::unordered_map<std::string, uint32_t> symbolMap;
    uint32_t idCounter = 1;                           // Counter to assign IDs to subtrees and variables
    int32_t cnt = 0;                                 // Counter for roles

    // Initialize the stack with the root node
    stack.push(root);

    while (!stack.empty())
    {
        Node n = stack.top();

        auto [it, inserted] = visited.emplace(n, false);
        if (inserted)
        {
            // First time seeing this node
            if (!n.isVar() && !n.isConst())
            {
                // Operator node
                // Push its unvisited children onto the stack
                for (size_t i = 0; i < n.getNumChildren(); ++i)
                {
                    Node child = n[i];
                    if (visited.find(child) == visited.end())
                    {
                        stack.push(child);
                    }
                }
            }
            else
            {
                // For variables and constants, mark as processed immediately
                it->second = true;
                stack.pop();
            }
        }
        else if (!it->second)
        {
            // Second time seeing this node, process it

            if (n.isVar())
            {
                // Variables are processed when included in operator nodes
                stack.pop();
            }
            else if (n.isConst())
            {
                // Constants are processed when included in operator nodes
                stack.pop();
            }
            else
            {
                // Operator node
                // Assign an ID to this node
                uint32_t id = idCounter++;
                subtreeIdMap[n] = id;

                // Build the encoding string
                std::string nodeEncoding = std::to_string(id) + ":";

                // Include operator kind
                cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(n.getKind());
                std::string opKind = cvc5::internal::kind::toString(k);
                nodeEncoding += opKind + ",";

                // For each child, include appropriate encoding
                for (size_t i = 0; i < n.getNumChildren(); ++i)
                {
                    Node child = n[i];
                    if (child.isConst())
                    {
                        // Include '^' followed by the constant value and '^'
                        std::string value = child.toString();
                        nodeEncoding += "^" + value + "^,";
                    }
                    else if (child.isVar())
                    {
                        // Update role map
                        std::string symbol = child.toString();
                        if (role.find(symbol) == role.end())
                        {
                            role[symbol] = cnt;
                        }
                        cnt++; // Increment cnt whether variable is new or not

                        // Assign ID to variable if not already assigned
                        if (symbolMap.find(symbol) == symbolMap.end())
                        {
                            symbolMap[symbol] = idCounter++;
                        }

                        // Include variable ID
                        uint32_t varId = symbolMap[symbol];
                        nodeEncoding += std::to_string(varId) + ",";
                    }
                    else
                    {
                        // Subtree: Include '|' followed by its ID and '|'
                        uint32_t childId = subtreeIdMap[child];
                        nodeEncoding += "|" + std::to_string(childId) + "|,";
                    }
                }

                // Remove the last comma
                if (n.getNumChildren() > 0)
                {
                    nodeEncoding.pop_back();
                }

                nodeEncoding += ";";

                // Concatenate the encoding directly
                encoding += nodeEncoding;

                // Mark as processed and pop
                it->second = true;
                stack.pop();
            }
        }
        else
        {
            // Node has already been processed
            stack.pop();
        }
    }
}






std::unique_ptr<NodeInfo> Daneshvar::getNodeInfo(const Node& node, uint32_t id)
{
    std::string encoding;
    std::map<std::string, int32_t> role;
    generateEncoding(node, encoding, role);
    return std::make_unique<NodeInfo>(node, encoding, role, 0, id);
}



bool sameClass(const NodeInfo& a, const NodeInfo& b) // Check if two nodes have the same encoding and pattern
{
    return a.encoding == b.encoding;
}


int numDigits(int n)
{
    if (n == 0)
    {
        return 1;
    }
    int count = 0;
    while (n > 0)
    {
        n = n / 10;
        count++;
    }
    return count;
}


Node rename(
    const Node& n,
    std::unordered_map<Node, Node>& freeVar2node,
    std::unordered_map<Node, Node>& boundVar2node,
    NodeManager* nodeManager,
    PreprocessingPassContext* d_preprocContext)
{
    // Map to cache normalized nodes
    std::unordered_map<Node, Node> normalized;

    // Stack for iterative traversal
    std::stack<Node> stack;

    // Map to keep track of visited nodes
    std::unordered_map<Node, bool> visited;

    // Initialize a global variable counter for variable renaming
    static int globalVarCounter = 0;

    // Push the root node onto the stack
    stack.push(n);

    while (!stack.empty())
    {
        Node current = stack.top();

        auto [it, inserted] = visited.emplace(current, false);
        if (inserted)
        {
            // First time seeing this node

            if (current.isConst() || current.isVar())
            {
                // For constants and variables, process immediately
                if (current.isVar())
                {
                    if (current.getKind() == cvc5::internal::Kind::BOUND_VARIABLE)
                    {
                        // Handle bound variable
                        auto it_bv = boundVar2node.find(current);
                        if (it_bv != boundVar2node.end())
                        {
                            normalized[current] = it_bv->second;
                        }
                        else
                        {
                            int id = globalVarCounter++;
                            std::string new_var_name =
                                "u" + std::string(8 - numDigits(id), '0') + std::to_string(id);
                            Node ret = nodeManager->mkBoundVar(new_var_name, current.getType());
                            boundVar2node[current] = ret;
                            normalized[current] = ret;
                        }
                    }
                    else
                    {
                        // Handle free variable using nodes as keys
                        auto it_fv = freeVar2node.find(current);
                        if (it_fv != freeVar2node.end())
                        {
                            normalized[current] = it_fv->second;
                        }
                        else
                        {
                            std::vector<Node> cnodes;
                            int id = globalVarCounter++;
                            std::string new_var_name =
                                "v" + std::string(8 - numDigits(id), '0') + std::to_string(id);
                            cnodes.push_back(nodeManager->mkConst(String(new_var_name, false)));
                            Node gt = nodeManager->mkConst(SortToTerm(current.getType()));
                            cnodes.push_back(gt);
                            Node ret = nodeManager->getSkolemManager()->mkSkolemFunction(
                                SkolemFunId::INPUT_VARIABLE, cnodes);
                            freeVar2node[current] = ret;
                            normalized[current] = ret;
                            d_preprocContext->addSubstitution(current, ret);
                        }
                    }
                }
                else
                {
                    // Constants are unchanged
                    normalized[current] = current;
                }

                // Mark as processed and pop from the stack
                it->second = true;
                stack.pop();
            }
            else
            {
                // Non-const, non-var node

                // For quantifiers, process bound variables immediately
                if (current.getKind() == cvc5::internal::Kind::FORALL ||
                    current.getKind() == cvc5::internal::Kind::EXISTS)
                {
                    Node bound_vars = current[0];

                    // Normalize bound variables and update boundVar2node
                    std::vector<Node> normalizedBoundVars;
                    for (size_t i = 0; i < bound_vars.getNumChildren(); ++i)
                    {
                        Node bv = bound_vars[i];
                        auto it_bv = boundVar2node.find(bv);
                        if (it_bv != boundVar2node.end())
                        {
                            normalized[bv] = it_bv->second;
                        }
                        else
                        {
                            int id = globalVarCounter++;
                            std::string new_var_name =
                                "u" + std::string(8 - numDigits(id), '0') + std::to_string(id);
                            Node newBv = nodeManager->mkBoundVar(new_var_name, bv.getType());
                            boundVar2node[bv] = newBv;
                            normalized[bv] = newBv;
                        }
                        normalizedBoundVars.push_back(normalized[bv]);
                    }

                    // Replace the bound variables in the quantifier
                    Node normalizedBoundVarList = nodeManager->mkNode(
                        cvc5::internal::Kind::BOUND_VAR_LIST, normalizedBoundVars);
                    normalized[bound_vars] = normalizedBoundVarList;
                }

                // Push unvisited children onto the stack
                for (int i = current.getNumChildren() - 1; i >= 0; i--)
                {
                    Node child = current[i];
                    if (visited.find(child) == visited.end())
                    {
                        stack.push(child);
                    }
                }

                // For APPLY_UF nodes, push the operator
                if (current.getKind() == cvc5::internal::Kind::APPLY_UF)
                {
                    Node op = current.getOperator();
                    if (visited.find(op) == visited.end())
                    {
                        stack.push(op);
                    }
                }

                // Leave 'it->second' as false; we'll process this node later
            }
        }
        else if (!it->second)
        {
            // Second time seeing this node, process it after its children

            // Prepare children for node creation
            std::vector<Node> children;

            if (current.getKind() == cvc5::internal::Kind::APPLY_UF)
            {
                // Handle operator for APPLY_UF nodes
                auto opIt = normalized.find(current.getOperator());
                Assert(opIt != normalized.end());
                children.push_back(opIt->second);
            }
            else if (current.getMetaKind() == metakind::PARAMETERIZED)
            {
                // For parameterized nodes, include the operator
                children.push_back(current.getOperator());
            }

            // Add normalized children
            for (size_t i = 0; i < current.getNumChildren(); ++i)
            {
                Node child = current[i];
                auto childIt = normalized.find(child);
                Assert(childIt != normalized.end());
                children.push_back(childIt->second);
            }

            // Create the new node with normalized children
            Node ret = nodeManager->mkNode(current.getKind(), children);
            normalized[current] = ret;

            // Mark as processed and pop from the stack
            it->second = true;
            stack.pop();
        }
        else
        {
            // Node has already been processed
            stack.pop();
        }
    }

    return normalized[n];
}















PreprocessingPassResult Daneshvar::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    TimerStat::CodeTimer codeTimer(d_statistics.d_passTime);

    // std::cout << "STARTING DANESHVAR PASS" << std::endl; 

    
    
    std::vector<std::unique_ptr<NodeInfo>> nodeInfos;

    /////////////////////////////////////////////////////////////
    // Step 1: Extract NodeInfo for each assertion
    uint32_t nextId = 0; 
    for (const Node& assertion : assertionsToPreprocess->ref())
    {
        // std::cout << "Assertion: " << assertion << std::endl;
        auto ni = getNodeInfo(assertion, nextId++);
        nodeInfos.push_back(std::move(ni));
        // std::cout << std::endl;
    }

    // std::cout << "Got NodeInfo for all assertions" << std::endl;
    // for (const auto&ni: nodeInfos)
    // {
    //     if (ni)
    //         ni->print();
    //     std::cout << std::endl;
    // }
    // /////////////////////////////////////////////////////////////

    

    /////////////////////////////////////////////////////////////
    // Step 2: Classify assertions into equivalence classes
    // Use NodeInfo pointers in eqClasses
    std::map<uint32_t, std::vector<NodeInfo*>> eqClasses;

    for (auto& niPtr : nodeInfos)
    {
        NodeInfo* current = niPtr.get();
        bool found = false;
        for (auto& [ec, eqClass] : eqClasses)
        {
            if (sameClass(*current, *eqClass[0]))
            {
                eqClass.push_back(current);
                current->equivClass = ec;
                found = true;
                break;
            }
        }
        if (!found)
        {
            eqClasses[current->id] = { current };
            current->equivClass = current->id;
        }
    }

    // for (const auto& [ec, eqClass] : eqClasses)
    // {
    //     std::cout << "Equivalence class " << ec << std::endl;
    //     for (const auto& ni : eqClass)
    //     {
    //         std::cout << "Node: " << ni->node << std::endl;
    //         std::cout << "Encoding: " << ni->encoding << std::endl;
    //         std::cout << std::endl;
    //     }
    //     std::cout << std::endl;
    // }

    /////////////////////////////////////////////////////////////


    

    /////////////////////////////////////////////////////////////
    // Step 3: Sort nodes based on encodings and super-patterns with customized comparison function
    std::map<std::string, std::vector<int32_t>> pattern; // Cache of patterns

    std::sort(nodeInfos.begin(), nodeInfos.end(),
        [&eqClasses, &pattern](const std::unique_ptr<NodeInfo>& a, const std::unique_ptr<NodeInfo>& b) {
            if (a->encoding != b->encoding) {
                return a->encoding < b->encoding;
            }

            // std::cout << "Comparing " << a->node << " and " << b->node << std::endl;


            // Iterating over roles in parallel since their sizes are guaranteed to be the same.
            auto itA = a->role.begin();
            auto itB = b->role.begin();

            while (itA != a->role.end() && itB != b->role.end()) {
                const std::string& symbolA = itA->first; 
                const std::string& symbolB = itB->first; 


                // Compute or retrieve patterns only once for each key
                auto getOrComputePattern = [&](const std::string& symbol) -> std::vector<int32_t> {
                    auto it = pattern.find(symbol);
                    if (it != pattern.end()) {
                        return it->second;
                    }

                    std::vector<int32_t> pat;
                    for (const auto& [ec, eqClass] : eqClasses) {
                        std::vector<int32_t> roles;
                        for (const NodeInfo* ni : eqClass) {
                            auto roleIt = ni->role.find(symbol);
                            roles.push_back(roleIt != ni->role.end() ? roleIt->second : static_cast<int32_t>(-1));
                        }

                        std::sort(roles.begin(), roles.end());
                        pat.insert(pat.end(), roles.begin(), roles.end());
                    }

                    pattern[symbol] = pat;
                    return pat;
                };

                // Retrieve patterns for both roles only once per iteration
                const std::vector<int32_t>& pat_a = getOrComputePattern(symbolA);
                const std::vector<int32_t>& pat_b = getOrComputePattern(symbolB);

                // std::cout << "Symbol A: " << symbolA << std::endl;
                // std::cout << "Symbol B: " << symbolB << std::endl;

                // std::cout << "Pattern A: ";
                // for (const auto& p : pat_a)
                // {
                //     std::cout << p << " ";
                // }
                // std::cout << std::endl;
                // std::cout << "Pattern B: ";
                // for (const auto& p : pat_b)
                // {
                //     std::cout << p << " ";
                // }
                // std::cout << std::endl << std::endl;

                // Compare patterns
                size_t minPatSize = std::min(pat_a.size(), pat_b.size());
                for (size_t j = 0; j < minPatSize; ++j) {
                    if (pat_a[j] != pat_b[j]) {
                        return pat_a[j] < pat_b[j];
                    }
                }

                ++itA;
                ++itB;
            }

            return false;
        });
    
    // /*
    // // for (const auto&ni: nodeInfos)
    // // {
    // //     if (ni)
    // //         ni->print();
    // //     std::cout << std::endl;
    // // }
    /////////////////////////////////////////////////////////////

    // std::cout << "renaming" << std::endl;

    //////////////////////////////////////////////////////////////////////
    // Step 4: Normalize the nodes based on the sorted order
    std::unordered_map<Node, Node> freeVar2node;
    // std::unordered_map<std::string, Node> boundVar2node;
    std::unordered_map<Node, Node> boundVar2node;
    NodeManager* nodeManager = NodeManager::currentNM();
    std::vector<Node> normalizedNodes;
    for (size_t i = 0; i < nodeInfos.size(); ++i)
    {
        Node renamed = rename(nodeInfos[i]->node, freeVar2node, boundVar2node, nodeManager, d_preprocContext);
        normalizedNodes.push_back(renamed);
    }
    //////////////////////////////////////////////////////////////////////

    // std::cout << "Renamed nodes" << std::endl;

    
    for (uint32_t i = 0; i < nodeInfos.size(); ++i)
    {
        // std::cout << "Normalized Node " << i << ": " << normalizedNodes[i] << std::endl;
        assertionsToPreprocess->replace(i, normalizedNodes[i]);
    }
    
    
    // std::cout << "FINISHED DANESHVAR PASS" << std::endl; // Note to make sure not timing out on passg

    

  return PreprocessingPassResult::NO_CONFLICT;
  
}


Daneshvar::Statistics::Statistics(StatisticsRegistry& reg)
    : d_passTime(reg.registerTimer("Daneshvar::pass_time"))
{
}




}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal