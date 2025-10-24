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
 *
 */

#include "preprocessing/passes/normalize.h"

#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/sort_to_term.h"
#include "util/string.h"
#include "expr/node_converter.h"
#include "expr/node_algorithm.h"
#include "util/statistics_registry.h"
#include "preprocessing/preprocessing_pass_context.h" 
#include "expr/cardinality_constraint.h"
#include "expr/normalize_sort_converter.h"
#include "expr/skolem_manager.h"

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

Normalize::Normalize(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "normalize"),
    d_statistics(statisticsRegistry())
    {};


void generateEncoding(
    const Node& root,
    std::string& encoding,
    std::map<std::string, int32_t>& role)
{
    std::stack<std::pair<Node, Node>> stack; // Pair of node, parent
    std::unordered_map<Node, bool> visited;
    std::unordered_map<Node, uint32_t> subtreeIdMap;
    std::unordered_map<std::string, uint32_t> symbolMap;
    uint32_t varIdCounter = 1;
    uint32_t subtreeIdCounter = 1;
    int32_t cnt = 0;

    std::vector<std::string> nodeEncodings;

    stack.push({root, root});

    while (!stack.empty())
    {
        // Get current node and its parent
        auto [n, parent] = stack.top();

        auto [it, inserted] = visited.emplace(n, false);
        if (inserted)
        {
            // First time seeing this node
            if (!n.isVar() && !n.isConst())
            {
                // Operator node
                for (size_t i = 0; i < n.getNumChildren(); ++i)
                {
                    Node child = n[i];
                    if (visited.find(child) == visited.end())
                    {
                        // Push child with current node n as its parent
                        stack.push({child, n});
                    }
                }
            }
            else
            {
                // For variables and constants, update role map and mark as processed immediately
                if (n.isVar())
                {
                    std::string symbol = std::to_string(n.getId());

                    if (role.find(symbol) == role.end() && parent.getKind() != cvc5::internal::Kind::INST_ATTRIBUTE) // Ignore variables in INST_ATTRIBUTE (qid)
                    {
                        role[symbol] = cnt;
                    }
                    cnt++; // Increment cnt whether variable is new or not
                }


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
                
                if (n.hasOperator())
                {
                    Node opNode = n.getOperator();
                    if (opNode.isVar())
                    {
                        std::string symbol = std::to_string(opNode.getId());

                        if (role.find(symbol) == role.end() && n.getKind() != cvc5::internal::Kind::INST_ATTRIBUTE)
                        {
                            role[symbol] = cnt;
                        }
                        cnt++; // Increment cnt whether variable is new or not
                    }
                }

                // Assign an ID to this node
                uint32_t id = subtreeIdCounter++;
                subtreeIdMap[n] = id;

                // Build the encoding string
                std::string nodeEncoding = std::to_string(id) + ":";

                // Include operator kind
                cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(n.getKind());
                std::string opKind = cvc5::internal::kind::toString(k);
                nodeEncoding += opKind + ",";

                // For each child, include appropriate encoding
                for (size_t i = n.getNumChildren(); i-- > 0;)
                {
                    Node child = n[i];
                    if (child.isConst())
                    {
                        // Include '^' followed by the constant value and '^'
                        std::string value = std::to_string(child.getId());
                        nodeEncoding += "^" + value + "^,";
                    }
                    else if (child.isVar())
                    {
                        // Update role map
                        std::string symbol = std::to_string(child.getId());

                        if (role.find(symbol) == role.end() && n.getKind() != cvc5::internal::Kind::INST_ATTRIBUTE)
                        {
                            role[symbol] = cnt;
                        }
                        cnt++; // Increment cnt whether variable is new or not

                        // Assign ID to variable if not already assigned
                        if (symbolMap.find(symbol) == symbolMap.end())
                        {
                            symbolMap[symbol] = varIdCounter++;
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

                // Collect the encoding instead of concatenating
                nodeEncodings.push_back(nodeEncoding);

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

    // Concatenate the node encodings in reverse order
    for (auto it = nodeEncodings.rbegin(); it != nodeEncodings.rend(); ++it)
    {
        encoding += *it;
    }
}







std::unique_ptr<NodeInfo> Normalize::getNodeInfo(const Node& node)
{
    std::string encoding;
    std::map<std::string, int32_t> role;
    generateEncoding(node, encoding, role);

    std::vector<std::pair<std::string, int32_t>> varNames(role.begin(), role.end());
        std::sort(varNames.begin(), varNames.end(), 
            [](const std::pair<std::string, int32_t>& A, const std::pair<std::string, int32_t>& B) {
                return A.second > B.second;
            });

    return std::make_unique<NodeInfo>(node, encoding, 0, role, varNames);
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
    std::unordered_map<std::string, std::string>& normalizedName,
    std::map<TypeNode, TypeNode> normalizedSorts,
    NodeManager* nodeManager,
    PreprocessingPassContext* d_preprocContext,
    NormalizeSortNodeConverter* sortNormalizer,
    bool& hasQID)
{
    // Map to cache normalized nodes
    std::unordered_map<Node, Node> normalized;

    // Stack for iterative traversal
    std::stack<Node> stack;

    // Map to keep track of visited nodes
    std::unordered_map<Node, bool> visited;

    // Initialize a global variable counter for variable renaming
    static int globalVarCounter = 0;

    // Initialize a variable counter for bound variables
    int boundVarCounter = 0;
    boundVar2node.clear();


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
                            // int id = globalVarCounter++;
                            int id = boundVarCounter++;
                            std::string new_var_name =
                                "u" + std::string(8 - numDigits(id), '0') + std::to_string(id);
                            // Node ret = nodeManager->mkBoundVar(new_var_name, current.getType());
                            // Node ret = nodeManager->mkBoundVar(new_var_name, 
                                // normalizedSorts.find(current.getType()) != normalizedSorts.end() ? normalizedSorts[current.getType()] : current.getType()
                            // );
                            Node ret = nodeManager->mkBoundVar(new_var_name, 
                                sortNormalizer->convertType(current.getType())
                            );

                            boundVar2node[current] = ret;
                            normalized[current] = ret;

                            // normalizedName[current.toString()] = new_var_name;
                            normalizedName[std::to_string(current.getId())] = new_var_name;
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
                            // cnodes.push_back(nodeManager->mkConst(String(new_var_name, false)));
                            // Node gt = nodeManager->mkConst(SortToTerm(
                            //     sortNormalizer->convertType(current.getType())
                            // ));

                            // cnodes.push_back(gt);
                            // Node ret = nodeManager->getSkolemManager()->mkInternalSkolemFunction(
                            //     InternalSkolemId::NORMALIZE_INPUT_VARIABLE,
                            //     sortNormalizer->convertType(current.getType()),
                            //     cnodes
                            // );

                            Node ret = nodeManager->getSkolemManager()->mkDummySkolem(
                                new_var_name,
                                sortNormalizer->convertType(current.getType()),
                                "normalized " + current.toString() + " to " + new_var_name,
                                SkolemFlags::SKOLEM_EXACT_NAME
                            );

                            freeVar2node[current] = ret;
                            normalized[current] = ret;
                            d_preprocContext->addSubstitution(current, ret);

                            // normalizedName[current.toString()] = new_var_name;
                            normalizedName[std::to_string(current.getId())] = new_var_name;
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

                if (!hasQID && current.getKind() == cvc5::internal::Kind::INST_ATTRIBUTE)
                {
                    // If any child is a variable, it's a qid
                    for (size_t i = 0; i < current.getNumChildren(); ++i)
                    {
                        Node child = current[i];
                        if (child.isVar())
                        {
                            hasQID = true;
                            break;  // Found at least one qid, no need to check further
                        }
                    }
                }


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
                            // int id = globalVarCounter++;
                            int id = boundVarCounter++;
                            std::string new_var_name =
                                "u" + std::string(8 - numDigits(id), '0') + std::to_string(id);
                            // Node newBv = nodeManager->mkBoundVar(new_var_name, bv.getType());
                            // boundVar2node[bv] = newBv;
                            // normalized[bv] = newBv;

                            Node ret = nodeManager->mkBoundVar(new_var_name, 
                                sortNormalizer->convertType(bv.getType())
                            );
                            boundVar2node[bv] = ret;
                            normalized[bv] = ret;
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







bool isTrivialEquality(const Node& n)
{
    if (n.getKind() == cvc5::internal::Kind::EQUAL)
    {
        const auto& lhs = n[0], rhs = n[1];
        if (lhs == rhs)
        {
            return true;
        }
    }
    return false;
}

bool isTrue(const Node& n)
{
    if (n.isConst() && n.getType().isBoolean())
    {
        return n.getConst<bool>();
    }
    return false;
}


// Same as getTypes. But this one colelcts types in a vector instead of an unordered_set

void collectTypes(TNode n,
              std::vector<TypeNode>& types,
              std::unordered_set<TNode>& visited,
              std::unordered_set<TypeNode>& mark
              )
{
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);


      if (mark.find(cur.getType()) == mark.end())
      {
        mark.insert(cur.getType());
        types.push_back(cur.getType());
      }

      
      // special cases where the type is not part of the AST
      if (cur.getKind() == Kind::CARDINALITY_CONSTRAINT)
      {

        if (mark.find(cur.getOperator().getConst<CardinalityConstraint>().getType()) == mark.end())
        {
            mark.insert(
                cur.getOperator().getConst<CardinalityConstraint>().getType());
            types.push_back(
                cur.getOperator().getConst<CardinalityConstraint>().getType());
        }

      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}




Node renameQid(
    const Node& n,
    std::unordered_map<Node, Node>& qidRenamed,
    std::unordered_map<std::string, std::string>& normalizedName,
    NodeManager* nodeManager)
{
  // Map to cache normalized nodes.
  std::unordered_map<Node, Node> normalized;
  // Map to track visited nodes (false: first visit; true: processed).
  std::unordered_map<Node, bool> visited;
  // Stack for iterative traversal.
  // Each element is a pair: (current node, its parent).
  std::stack<std::pair<Node, Node>> stack;
  // Global counter for qid renaming (starting at 1).
  static int qidCounter = 1;

  // Push the root node with a null parent.
  stack.push({n, Node()});

  while (!stack.empty())
  {
    // Get current node and its parent.
    auto [current, parent] = stack.top();

    // Try inserting current node into visited.
    auto [it, inserted] = visited.emplace(current, false);
    if (inserted)
    {
      // First time seeing this node.
      if (current.isConst() || current.isVar())
      {
        // Check if current is a variable and qualifies as a qid.
        // A qid is defined as a variable whose parent has kind INST_ATTRIBUTE.
        if (current.isVar() &&
            (!parent.isNull() && parent.getKind() == cvc5::internal::Kind::INST_ATTRIBUTE))
        {
          // If we already renamed this variable, use that renaming.
          auto it_qid = qidRenamed.find(current);
          if (it_qid != qidRenamed.end())
          {
            normalized[current] = it_qid->second;
          }
          else
          {
            // Otherwise, generate a new name "q00000001", "q00000002", etc.
            std::string new_var_name =
              "q" + std::string(8 - numDigits(qidCounter), '0') + std::to_string(qidCounter);
            qidCounter++;

            // Create a new dummy skolem (or qid variable) with the new name.
            Node ret = nodeManager->getSkolemManager()->mkDummySkolem(
                new_var_name,
                current.getType(),
                "renamed qid " + current.toString() + " to " + new_var_name,
                SkolemFlags::SKOLEM_EXACT_NAME
            );
            qidRenamed[current] = ret;
            normalized[current] = ret;
            // normalizedName[current.toString()] = new_var_name;
            normalizedName[std::to_string(current.getId())] = new_var_name;
          }
        }
        else
        {
          // Otherwise, leave the node unchanged.
          normalized[current] = current;
        }
        // Mark this node as processed.
        visited[current] = true;
        stack.pop();
      }
      else
      {
        // For non-const and non-var nodes, push their children (with current as parent)
        // in reverse order to preserve left-to-right traversal.
        for (int i = current.getNumChildren() - 1; i >= 0; --i)
        {
          Node child = current[i];
          stack.push({child, current});
        }
        // For APPLY_UF nodes, push the operator.
        if (current.getKind() == cvc5::internal::Kind::APPLY_UF)
        {
          Node op = current.getOperator();
          stack.push({op, current});
        }
        // Leave the node for a second visit.
      }
    }
    else if (!it->second)
    {
      // Second time visiting the node: all its children have been processed.
      std::vector<Node> children;
      if (current.getKind() == cvc5::internal::Kind::APPLY_UF)
      {
        // Add the normalized operator.
        auto opIt = normalized.find(current.getOperator());
        Assert(opIt != normalized.end());
        children.push_back(opIt->second);
      }
      else if (current.getMetaKind() == metakind::PARAMETERIZED)
      {
        // For parameterized nodes, include the operator.
        children.push_back(current.getOperator());
      }
      // Add normalized children.
      for (size_t i = 0; i < current.getNumChildren(); i++)
      {
        Node child = current[i];
        auto childIt = normalized.find(child);
        Assert(childIt != normalized.end());
        children.push_back(childIt->second);
      }
      // Reconstruct the node with its normalized children.
      Node ret = nodeManager->mkNode(current.getKind(), children);
      normalized[current] = ret;
      visited[current] = true;
      stack.pop();
    }
    else
    {
      // Node already processed.
      stack.pop();
    }
  }

  return normalized[n];
}








PreprocessingPassResult Normalize::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    TimerStat::CodeTimer codeTimer(d_statistics.d_passTime);

    // Step 1: Get NodeInfo for all assertions
    
    std::vector<std::shared_ptr<NodeInfo>> nodeInfos;
    for (const Node& assertion : assertionsToPreprocess->ref())
    {
        if (isTrivialEquality(assertion) || isTrue(assertion))
        {
            continue;
        }
        auto ni = getNodeInfo(assertion);
        nodeInfos.push_back(std::move(ni));
    }

    // Step 2: Store assertions in which every symbol occurs (will be used for super-pattern computation)
    
    std::unordered_map<std::string, std::vector<std::shared_ptr<NodeInfo>>> symbolOccurrences;
    for (const auto& nodeInfo : nodeInfos) {
        for (const auto& [symbol, _] : nodeInfo->varNames) {
            symbolOccurrences[symbol].push_back(nodeInfo);
        }
    }

    // Step 3: Classify assertions into equivalence classes
    
    std::vector<std::vector<NodeInfo*>> eqClasses;
    std::unordered_map<std::string, uint32_t> seenEncodings;
    for (auto& niPtr : nodeInfos) {
        NodeInfo* current = niPtr.get();
        auto it = seenEncodings.find(current->encoding);
        if (it != seenEncodings.end()) {
            eqClasses[it->second].push_back(current);
        } else {
            seenEncodings[current->encoding] = eqClasses.size();
            std::vector<NodeInfo*> newClass;
            newClass.push_back(current);
            eqClasses.push_back(std::move(newClass));
        }
    }
    // Step 3: Sort equivalence classes based on encodings
    std::sort(eqClasses.begin(), eqClasses.end(),
        [](const std::vector<NodeInfo*>& a, const std::vector<NodeInfo*>& b) {
            return a[0]->encoding > b[0]->encoding;
        });

    // Set IDs for all nodes. Used for super-pattern computation
    
    uint32_t idCnt = 0;
    for (const auto& eqClass : eqClasses)
    {
        for (const auto& ni : eqClass)
        {
            ni->setId(idCnt);
        }
        idCnt++;
    }
    // Step 4: Sort within equivalence classes
    std::unordered_map<std::string, std::vector<std::vector<int32_t>>> patternCache; // Cache of superpatterns


    for (auto& eqClass : eqClasses) {
        std::sort(eqClass.begin(), eqClass.end(),
            [&eqClasses, &patternCache, &symbolOccurrences](NodeInfo* a, NodeInfo* b) {

                auto itA = a->varNames.begin();
                auto itB = b->varNames.begin();

                while (itA != a->varNames.end() && itB != b->varNames.end()) {
                    const std::string& symbolA = itA->first; 
                    const std::string& symbolB = itB->first; 

                    auto getOrComputeSuperpattern = [&](const std::string &symbol) -> const std::vector<std::vector<int32_t>>& {
                        auto it = patternCache.find(symbol);
                        if (it != patternCache.end()) {
                            return it->second; // Return cached superpattern if it exists
                        }

                        // Initialize the superpattern with empty vectors for each segment
                        std::vector<std::vector<int32_t>> superpattern(eqClasses.size());

                        auto symbolIt = symbolOccurrences.find(symbol);
                        Assert(symbolIt != symbolOccurrences.end());

                        // Iterate over all occurrences of the symbol
                        for (const auto& nodeInfo : symbolIt->second) {
                            auto roleIt = nodeInfo->role.find(symbol);
                            Assert(roleIt != nodeInfo->role.end());

                            // Get the equivalence class ID for this node
                            uint32_t eqClassId = nodeInfo->id;

                            // Push the non-negative value to the corresponding segment in the superpattern
                            superpattern[eqClassId].push_back(roleIt->second);
                        }

                        // Sort each segment in the superpattern and compute the -1 count
                        for (size_t i = 0; i < superpattern.size(); ++i) {
                            std::sort(superpattern[i].begin(), superpattern[i].end());
                            // The count of -1s is the size of the equivalence class minus the number of non-negative values
                            superpattern[i].insert(superpattern[i].begin(), eqClasses[i].size() - superpattern[i].size());
                        }

                        // Cache the superpattern
                        auto &ret = patternCache[symbol];
                        ret = std::move(superpattern);
                        return ret;
                    };

                    if (symbolA == symbolB) {
                        ++itA;
                        ++itB;
                        continue;
                    }

                    const std::vector<std::vector<int32_t>>& superpatternA = getOrComputeSuperpattern(symbolA);
                    const std::vector<std::vector<int32_t>>& superpatternB = getOrComputeSuperpattern(symbolB);

                    // Compare superpatterns segment by segment
                    for (size_t i = 0; i < superpatternA.size(); ++i) {
                        const auto& patA = superpatternA[i];
                        const auto& patB = superpatternB[i];

                        // Compare the count of -1s in the segment
                        if (patA[0] != patB[0]) {
                            return patA[0] < patB[0];
                        }

                        // Compare the non-negative values in the segment
                        for (size_t j = 1; j < patA.size() && j < patB.size(); ++j) {
                            if (patA[j] != patB[j]) {
                                return patA[j] < patB[j];
                            }
                        }

                        // If one segment has more non-negative values, it is considered greater
                        if (patA.size() != patB.size()) {
                            return patA.size() < patB.size();
                        }
                    }

                    ++itA;
                    ++itB;
                }

                // Handle cases where one iterator reaches the end before the other
                if (itA != a->varNames.end()) return true;
                if (itB != b->varNames.end()) return false;

                return false;
            });
    }

    
    std::vector<TypeNode> types;
    std::unordered_set<TNode> visited;
    std::unordered_set<TypeNode> mark;
    for (const std::vector<NodeInfo*>& eqClass : eqClasses) 
    {
        for (NodeInfo* nodeInfo : eqClass) 
        {
            collectTypes(nodeInfo->node, types, visited, mark);
        }
    }

    
    std::map<TypeNode, TypeNode> normalizedSorts;
    int sortCounter = 0;
    for (const TypeNode& ctn : types)
    {
        if (ctn.isUninterpretedSort() && ctn.getNumChildren() == 0)
        {
            std::string new_sort_name = "S" + std::string(8 - numDigits(sortCounter), '0') + std::to_string(sortCounter);
            sortCounter++;
            TypeNode new_sort = nodeManager()->mkSort(new_sort_name);
            normalizedSorts[ctn] = new_sort;
        }
    }

    NormalizeSortNodeConverter* sortNormalizer = new NormalizeSortNodeConverter(normalizedSorts, nodeManager());

    // Step 5: Normalize the nodes based on the sorted order
    
    std::unordered_map<Node, Node> freeVar2node;
    std::unordered_map<Node, Node> boundVar2node;
    // NodeManager* nodeManager = NodeManager::currentNM();
    std::unordered_map<std::string, std::string> normalizedName;

    bool hasQID = false;
    for (const auto& eqClass : eqClasses)
    {
        for (const auto& ni : eqClass)
        {            
            Node renamed = rename(ni->node, freeVar2node, boundVar2node, normalizedName, normalizedSorts, nodeManager(), d_preprocContext, sortNormalizer, hasQID);  
            ni->node = renamed;          
        }
    }

    // Step 6: Sort the nodes within each equivalence class based on the normalized node names
    
    for (auto& eqClass : eqClasses)
    {
        std::sort(eqClass.begin(), eqClass.end(),
            [&normalizedName](NodeInfo* a, NodeInfo* b) {
                // Loop on the roles, retrieve the normalized names and compare them

                // varNames has old names before renaming. We need to sort based on the new names

                size_t sz = std::min(a->varNames.size(), b->varNames.size()); // They are the same size
                for (size_t i = 0; i < sz; ++i)
                {
                    const std::string& symbolA = a->varNames[i].first;
                    const std::string& symbolB = b->varNames[i].first;
                    const std::string& normNameA = normalizedName[symbolA];
                    const std::string& normNameB = normalizedName[symbolB];

                    if (normNameA != normNameB)
                    {
                        return normNameA < normNameB;
                    }
                }

                return false;
            });
    }

    // Step 7: Reassign qid top to bottom
    
    std::unordered_map<Node, Node> qidRenamed;
    if (hasQID)
    {
        for (const auto& eqClass : eqClasses)
        {
            for (const auto& ni : eqClass)
            {            
                Node renamed = renameQid(ni->node, qidRenamed, normalizedName, nodeManager());  
                ni->node = renamed;          
            }
        }
    }

    // Replace assertions with normalized versions
    uint32_t idx = 0;
    for (const auto& eqClass: eqClasses)
    {
        for (const auto& ni : eqClass)
        {
            assertionsToPreprocess->replace(idx++, ni->node);
        }
    }
    assertionsToPreprocess->resize(idx);

    return PreprocessingPassResult::NO_CONFLICT;
  
}


Normalize::Statistics::Statistics(StatisticsRegistry& reg)
    : d_passTime(reg.registerTimer("Normalize::pass_time"))
{
}




}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal