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

void dfs(const Node& n, std::string& encoding, std::vector<std::string>& varNames)
{
    if (n.isVar())
    {
        std::string varname = n.toString();
        encoding += "V;";
        varNames.push_back(varname);
        return;
    }
    if (n.isConst())
    {
        encoding += n.toString() + ";";
        return;
    }

    cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(n.getKind());
    std::string boz = cvc5::internal::kind::toString(k);
    encoding += boz + ";";
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        dfs(n[i], encoding, varNames);
    }
}




int getRole(std::string var, NodeInfo n)
{
    auto it = n.role.find(var);
    if (it != n.role.end())
    {
        return it->second;
    }
    return 0;
}

NodeInfo getNodeInfo(const Node& n, unsigned ecId_ass, unsigned ecId_op)
{
    std::string encoding = "";
    std::vector<std::string> varNames; 
    dfs(n, encoding, varNames);
    encoding += "\n";

    std::vector<int> pat;
    std::map<std::string, int> varMap;
    std::map<std::string, int> role;
    int id = 1;
    for (size_t i = 0; i < varNames.size(); ++i)
    {
        if (varMap.find(varNames[i]) == varMap.end())
        {
            varMap[varNames[i]] = id++;
            role[varNames[i]] = varMap[varNames[i]];
            // std::cout << "Role of " << varNames[i] << " is " << role[varNames[i]] << std::endl;
        }
        pat.push_back(varMap[varNames[i]]);
    }
    // std::cout << "---------------------------------" << std::endl;
    return NodeInfo(n, encoding, pat, varNames, role, ecId_ass, ecId_op);
}


bool nodeInfoCmp(const NodeInfo& a, const NodeInfo& b)
{
    if (a.encoding == b.encoding)
    {
        AssertArgument(a.pat.size() == b.pat.size(), a.toString() + " and " + b.toString() + " have the same encoding but different variable sequence size");
        size_t n = a.pat.size();
        for (size_t i = 0; i < n; i++)
        {
            if (a.pat[i] != b.pat[i])
            {
                return a.pat[i] < b.pat[i];
            }
        }
        // Now we have two alpha-equivalent nodes. Compare lexico-graphically
        n = a.varNames.size();
        for (size_t i = 0; i < n; i++)
        {
            if (a.varNames[i] != b.varNames[i])
            {
                return a.varNames[i] < b.varNames[i];
            }
        }
        // Same encoding, same pattern, same variable sequence. We don't care at this point :)
        return false;
    }
    return a.encoding < b.encoding;
}




bool operandsCmpR1(std::map<int, std::vector<NodeInfo>>& ec_ass,
                   std::map<int, std::vector<NodeInfo>>& ec_oper,
                   const NodeInfo& nia,
                   const NodeInfo& nib)
 {
    Node a = nia.node, b = nib.node;

    if (nia.encoding != nib.encoding)
    {
        return nia.encoding < nib.encoding;
    } 
    AssertArgument(nia.pat.size() == nib.pat.size(), nia.toString() + " and " + nib.toString() + " have the same encoding but different variable sequence size");
    for (size_t i = 0; i < nia.pat.size(); i++)
    {
        if (nia.pat[i] != nib.pat[i])
        {
            return nia.pat[i] < nib.pat[i];
        }
    }


    // Now we know that they belong to the same equivalent class
    AssertArgument(nia.equivClassId_operands == nib.equivClassId_operands, nia.toString() + " and " + nib.toString() + " have the same encoding and pattern but different equivalent class id for operands");

    // Calculate super-pattern of diff pairs of variables in the next equivalent classes and compare them
    for (size_t i = 0; i < nia.varNames.size(); ++i)
    {
        if (nia.varNames[i] == nib.varNames[i])
        {
            continue;
        }
        std::string var_a = nia.varNames[i], var_b = nib.varNames[i]; // first different variables in a and b
        
        int ecId_operands = nia.equivClassId_operands; // = b.equivClassId_operands
        std::vector<int> spat_a, spat_b;
        for (int j = ecId_operands; ec_oper[j].size() > 0; ++j)
        {
            std::vector<int> pat_j_a, pat_j_b;
            for (NodeInfo curr : ec_oper[j])
            {
                pat_j_a.push_back(getRole(var_a, curr));
                pat_j_b.push_back(getRole(var_b, curr));
            }
            sort(pat_j_a.begin(), pat_j_a.end());
            sort(pat_j_b.begin(), pat_j_b.end());
            // Append pattern of var_a in ec_oper[j] to spat_a
            for (size_t k = 0; k < pat_j_a.size(); k++)
            {
                spat_a.push_back(pat_j_a[k]);
                spat_b.push_back(pat_j_b[k]);
            }
        }

        // Compare the super-patterns
        size_t n = spat_a.size();
        for (size_t j = 0; j < n; j++)
        {
            if (spat_a[j] != spat_b[j])
            {
                return spat_a[j] < spat_b[j];
            }
        }
    }


    return false;
}




bool equivClassCalcCmp(const NodeInfo& a, const NodeInfo& b)
{
    if (a.encoding != b.encoding)
    {
        return a.encoding < b.encoding;
    }
    int n = a.pat.size();
    for (int i = 0; i < n; i++)
    {
        if (a.pat[i] != b.pat[i])
        {
            return a.pat[i] < b.pat[i];
        }
    }
    
    return false;
}

bool complexCmp(std::map<int, std::vector<NodeInfo>>& ec_ass,
                std::map<int, std::vector<NodeInfo>>& ec_oper,
                const NodeInfo& a,
                const NodeInfo& b)
{
    if (a.equivClassId_ass  != b.equivClassId_ass)
    {
        return a.equivClassId_ass < b.equivClassId_ass;
    }


    // a and b belong to the same class

    // Calculate super-pattern of diff pairs of variables in the next equivalent classes and compare them
    int ecId_ass = a.equivClassId_ass; // also b.equivClassId_ass
    std::vector<int> spat_a, spat_b;
    for (size_t i = 0; i < a.varNames.size(); ++i)
    {
        if (a.varNames[i] == b.varNames[i])
        {
            continue;
        }
        std::string var_a = a.varNames[i], var_b = b.varNames[i]; // first different variables in a and b
        // Calculate super-pattern of var_a and var_b in next equivalent classes
        spat_a.clear();
        spat_b.clear();
        for (int j = ecId_ass; ec_ass[j].size() > 0; ++j)
        {
            std::vector<int> pat_j_a, pat_j_b;
            for (NodeInfo curr : ec_ass[j])
            {
                pat_j_a.push_back(getRole(var_a, curr));
                pat_j_b.push_back(getRole(var_b, curr));
            }


            sort(pat_j_a.begin(), pat_j_a.end());
            sort(pat_j_b.begin(), pat_j_b.end());

            for (size_t k = 0; k < pat_j_a.size(); k++)
            {
                spat_a.push_back(pat_j_a[k]);
                spat_b.push_back(pat_j_b[k]);
            }
        }
    }

    // Compare the super-patterns
    size_t n = spat_a.size();
    for (size_t i = 0; i < n; i++)
    {
        if (spat_a[i] != spat_b[i])
        {
            return spat_a[i] < spat_b[i];
        }
    }


    return false;   
}



// Return vector index >= 0 (from where the list of children is commutative)
// if true, else -1.
int isCommutative(cvc5::internal::Kind k)
{
    if (k == cvc5::internal::Kind::ADD) 
        return 0;
    if (k == cvc5::internal::Kind::MULT) 
        return 0;
    if (k == cvc5::internal::Kind::AND)
        return 0;
    if (k == cvc5::internal::Kind::OR)
        return 0;
    if (k == cvc5::internal::Kind::XOR)
        return 0;
    if (k == cvc5::internal::Kind::DISTINCT)
        return 0;
    if (k == cvc5::internal::Kind::EQUAL) 
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_AND)
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_OR)
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_XOR)
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_NAND)
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_NOR)
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_COMP)
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_ADD)
        return 0;
    if (k == cvc5::internal::Kind::BITVECTOR_MULT)
        return 0;
    if (k == cvc5::internal::Kind::FLOATINGPOINT_EQ)
        return 0;
    if (k == cvc5::internal::Kind::FLOATINGPOINT_ADD)
        return 1;
    if (k == cvc5::internal::Kind::FLOATINGPOINT_MULT)
        return 1;
    return -1;
}

bool sameClass(const NodeInfo& a, const NodeInfo& b)
{
    if (a.encoding != b.encoding)
    {
        return false;
    }
    int n = a.pat.size();
    for (int i = 0; i < n; i++)
    {
        if (a.pat[i] != b.pat[i])
        {
            return false;
        }
    }
    return true;
}



Node sortOperands(std::map<int, std::vector<NodeInfo>>& ec_ass,
                  std::map<int, std::vector<NodeInfo>>& ec_oper,
                  const NodeInfo& ni)
{
    Node n = ni.node;
    if (n.isVar() || n.isConst()) {
        return n;
    }

    std::stack<NodeInfo> toVisit;

    std::map<Node, std::vector<NodeInfo>> nodeChildrenMap;

    std::map<Node, Node> processedNodes;

    toVisit.push(ni);

    while (!toVisit.empty()) {
        NodeInfo currentNodeInfo = toVisit.top();
        Node currentNode = currentNodeInfo.node;

        if (processedNodes.find(currentNode) != processedNodes.end()) {
            toVisit.pop();
            continue;
        }

        if (currentNode.isVar() || currentNode.isConst()) {
            processedNodes[currentNode] = currentNode;
            toVisit.pop();
            continue;
        }

        if (nodeChildrenMap.find(currentNode) == nodeChildrenMap.end()) {
            std::vector<NodeInfo> child;
            for (size_t i = 0; i < currentNode.getNumChildren(); i++) {
                NodeInfo childInfo = getNodeInfo(currentNode[i], -1, -1);
                child.push_back(childInfo);
                toVisit.push(childInfo);
            }
            nodeChildrenMap[currentNode] = child;

            if (currentNode.getKind() == cvc5::internal::Kind::APPLY_UF) {
                NodeInfo operatorInfo = getNodeInfo(currentNode.getOperator(), -1, -1);
                toVisit.push(operatorInfo);
            }
            continue;
        }

        toVisit.pop();

        std::vector<NodeInfo> child = nodeChildrenMap[currentNode];
        int commutative = isCommutative(currentNode.getKind());

        if (commutative != -1) {
            ec_oper.clear();
            std::sort(child.begin() + commutative, child.end(), equivClassCalcCmp);

            int ecId_operands = 1;
            child[commutative].equivClassId_operands = ecId_operands;
            ec_oper[ecId_operands].push_back(child[commutative]);
            for (size_t i = commutative + 1; i < child.size(); i++) {
                if (!sameClass(child[i], child[i - 1])) {
                    ecId_operands++;
                }
                child[i].equivClassId_operands = ecId_operands;
                ec_oper[ecId_operands].push_back(child[i]);
            }


        std::sort(child.begin() + commutative, child.end(),
          [&ec_ass, &ec_oper](const NodeInfo& nia, const NodeInfo& nib) {
              return operandsCmpR1(ec_ass, ec_oper, nia, nib);
          });

        }

        std::vector<Node> operands;

        if (currentNode.getMetaKind() == metakind::PARAMETERIZED) {
            operands.push_back(currentNode.getOperator());
        }

        for (size_t i = 0; i < child.size(); i++) {
            operands.push_back(processedNodes[child[i].node]);
        }

        Node sortedNode = NodeManager::currentNM()->mkNode(currentNode.getKind(), operands);
        processedNodes[currentNode] = sortedNode;
    }

    return processedNodes[n];
}



Node fixflips(Node n)
{
    if (n.isVar() || n.isConst())
    {
        return n;
    }
    if (n.getKind() == cvc5::internal::Kind::GT)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::LT, n[1], n[0]);
    }
    if (n.getKind() == cvc5::internal::Kind::GEQ)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::LEQ, n[1], n[0]);
    }
    if (n.getKind() == cvc5::internal::Kind::BITVECTOR_UGT)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::BITVECTOR_ULT, n[1], n[0]);
    }
    if (n.getKind() == cvc5::internal::Kind::BITVECTOR_UGE)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::BITVECTOR_ULE, n[1], n[0]);
    }
    if (n.getKind() == cvc5::internal::Kind::BITVECTOR_SGT)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::BITVECTOR_SLT, n[1], n[0]);
    }
    if (n.getKind() == cvc5::internal::Kind::BITVECTOR_SGE)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::BITVECTOR_SLE, n[1], n[0]);
    }
    if (n.getKind() == cvc5::internal::Kind::FLOATINGPOINT_GT)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::FLOATINGPOINT_LT, n[1], n[0]);
    }
    if (n.getKind() == cvc5::internal::Kind::FLOATINGPOINT_GEQ)
    {
        return NodeManager::currentNM()->mkNode(cvc5::internal::Kind::FLOATINGPOINT_LEQ, n[1], n[0]);
    }

    std::vector<Node> operands;

    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
        operands.push_back(n.getOperator());
    }
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        operands.push_back(fixflips(n[i]));
    }

    return NodeManager::currentNM()->mkNode(n.getKind(), operands);
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



Node rename(const Node& n, 
            std::map<std::string, Node>& freeVar2node, 
            std::map<std::string, Node>& boundVar2node, 
            NodeManager* nodeManager,
            PreprocessingPassContext* d_preprocContext)
{
    std::map<Node, Node> normalized;
    std::stack<Node> stack1, stack2;
    std::stack<std::map<std::string, Node>> scopeStack;

    stack1.push(n);
    scopeStack.push(boundVar2node); // Initialize with the global scope

    while (!stack1.empty()) {
        Node current = stack1.top();
        stack1.pop();
        stack2.push(current);

        if (current.isConst() || current.isVar()) {
            continue;
        }

        if (current.getKind() == cvc5::internal::Kind::APPLY_UF) {
            stack1.push(current.getOperator());
        }

        for (size_t i = 0; i < current.getNumChildren(); i++) {
            stack1.push(current[i]);
        }
    }

    while (!stack2.empty()) {
        Node current = stack2.top();
        stack2.pop();

        if (current.isConst()) {
            normalized[current] = current;
            continue;
        }

        if (current.isVar()) {
            if (current.getKind() == cvc5::internal::Kind::BOUND_VARIABLE) {
                auto& currentScope = scopeStack.top();

                if (currentScope.find(current.toString()) != currentScope.end()) {
                    normalized[current] = currentScope[current.toString()];
                } else {
                    int id = currentScope.size();
                    std::string new_var_name = "u" + std::string(5 - numDigits(id), '0') + std::to_string(id);
                    Node ret = nodeManager->mkBoundVar(new_var_name, current.getType());
                    currentScope[current.toString()] = ret;
                    normalized[current] = ret;
                }
            } else {
                if (freeVar2node.find(current.toString()) != freeVar2node.end()) {
                    normalized[current] = freeVar2node[current.toString()];
                } else {
                    std::vector<Node> cnodes;
                    int id = freeVar2node.size();
                    std::string new_var_name = "v" + std::string(5 - numDigits(id), '0') + std::to_string(id);
                    cnodes.push_back(nodeManager->mkConst(String(new_var_name, false)));
                    Node gt = nodeManager->mkConst(SortToTerm(current.getType()));
                    cnodes.push_back(gt);
                    Node ret = nodeManager->getSkolemManager()->mkSkolemFunction(SkolemFunId::INPUT_VARIABLE, cnodes);
                    freeVar2node[current.toString()] = ret;
                    normalized[current] = ret;
                    d_preprocContext->addSubstitution(current, ret);
                }
            }
            continue;
        }

        std::vector<Node> children;
        if (current.getKind() == cvc5::internal::Kind::APPLY_UF) {
            children.push_back(normalized[current.getOperator()]);
        } else if (current.getMetaKind() == metakind::PARAMETERIZED) {
            children.push_back(current.getOperator());
        }

        for (size_t i = 0; i < current.getNumChildren(); i++) {
            children.push_back(normalized[current[i]]);
        }

        if (current.getKind() == cvc5::internal::Kind::FORALL || current.getKind() == cvc5::internal::Kind::EXISTS) {
            Node bound_vars = current[0];
            std::map<std::string, Node> newScope = scopeStack.top(); // Create a new scope

            for (size_t i = 0; i < bound_vars.getNumChildren(); i++) {
                if (newScope.find(bound_vars[i].toString()) != newScope.end()) {
                    newScope.erase(bound_vars[i].toString()); // Remove the bound variable from the parent scope
                }
            }

            scopeStack.push(newScope); // Push the new scope onto the stack

            // After processing the bound variables, we pop the scope stack
            scopeStack.pop();
        }

        Node ret = nodeManager->mkNode(current.getKind(), children);
        normalized[current] = ret;
    }

    return normalized[n];
}





PreprocessingPassResult Daneshvar::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    TimerStat::CodeTimer codeTimer(d_statistics.d_passTime);

    std::vector<NodeInfo> nodeInfos, prv_nodeInfos;


    /////////////////////////////////////////////////////////////
    // Step 1: Fix anti-symmetric operators
    for (const Node& assertion : assertionsToPreprocess->ref())
    {
        Node curr = fixflips(assertion);
        nodeInfos.push_back(getNodeInfo(curr, -1, -1));
    }
    /////////////////////////////////////////////////////////////




    /////////////////////////////////////////////////////////////
    // Step 2: Sort operands of commutative operators using 1. encoding 2. pattern 3. super-patterns
    prv_nodeInfos = nodeInfos;
    nodeInfos.clear();

    for (NodeInfo ni: prv_nodeInfos)
    {
        Node curr = sortOperands(d_ec_ass, d_ec_oper, ni);
        nodeInfos.push_back(getNodeInfo(curr, -1, -1));
    }
    /////////////////////////////////////////////////////////////



    /////////////////////////////////////////////////////////////    
    // Step 3: Sort based on encoding and pattern to calculate equivalence classes
    sort(nodeInfos.begin(), nodeInfos.end(), equivClassCalcCmp); 
    /////////////////////////////////////////////////////////////








    /////////////////////////////////////////////////////////////
    // Step 4: Calculate equivalence classes for assertions
    unsigned ecId_ass = 1;
    nodeInfos[0].equivClassId_ass = ecId_ass;
    d_ec_ass[ecId_ass].push_back(nodeInfos[0]);
    // std::cout << "EC1" << std::endl;
    // std::cout << nodeInfos[0].node << std::endl;
    for (size_t i = 1; i < nodeInfos.size(); i++)
    {
        if (!sameClass(nodeInfos[i], nodeInfos[i - 1]))
        {
            ecId_ass++;
            // std::cout << "******" << std::endl;
            // std::cout << "EC" << ecId_ass << std::endl;
        }
        nodeInfos[i].equivClassId_ass = ecId_ass;
        d_ec_ass[ecId_ass].push_back(nodeInfos[i]);
        // std::cout << nodeInfos[i].encoding << std::endl;
        // std::cout << nodeInfos[i].node << std::endl;
    }
    // std::cout << "CALCULATED EQUIVALENCE CLASSES" << std::endl;
    /////////////////////////////////////////////////////////////






    /////////////////////////////////////////////////////////////
    // Step 5: Sort the assertions based on our super complex metric!
    prv_nodeInfos = nodeInfos;
    nodeInfos.clear();
    for (NodeInfo ni: prv_nodeInfos)
    {
        nodeInfos.push_back(getNodeInfo(ni.node, ni.equivClassId_ass, -1));
    }
    sort(nodeInfos.begin(),
         nodeInfos.end(),
         [this](const auto& a, const auto& b) {
           return complexCmp(d_ec_ass, d_ec_oper, a, b);
         });
    // std::cout << "SORTED ASSERTIONS" << std::endl;
    /////////////////////////////////////////////////////////////







    /////////////////////////////////////////////////////////////
    // Step 6: Sort the operands once again
    // prv_nodeInfos = nodeInfos;
    // nodeInfos.clear();
    // for (NodeInfo ni: prv_nodeInfos)
    // {
    //     Node curr = sortOp3(ni);
    //     nodeInfos.push_back(getNodeInfo(curr, ni.equivClassId_ass, -1));
    // }
    /////////////////////////////////////////////////////////////









    /////////////////////////////////////////////////////////////
    // Step 7: Variable normalization left ro right top to bottom
    prv_nodeInfos = nodeInfos;
    nodeInfos.clear();

    std::map<std::string, Node> freeVar2node;
    std::map<std::string, Node> boundVar2node;
    NodeManager* nodeManager = NodeManager::currentNM();
    for (NodeInfo ni: prv_nodeInfos)
    {
        Node renamed = rename(ni.node, freeVar2node, boundVar2node, nodeManager, d_preprocContext);
        nodeInfos.push_back(getNodeInfo(renamed, -1, -1));
    }
    /////////////////////////////////////////////////////////////





    /////////////////////////////////////////////////////////////
    // Step 8: Final sort with new names. NEEDED?
    // sort(nodeInfos.begin(), nodeInfos.end(), nodeInfoCmp); 
    // std::cout << "FINAL SORT WITHIN EQUIVALENCE CLASSES" << std::endl;
    ///////////////////////////////////////////////////////////




    /*
    // Step 5: Final renaming

    // prv_nodeInfos = nodeInfos;
    // nodeInfos.clear();

    // freeVar2node.clear();
    // boundVar2node.clear();
    // for (size_t i = 0; i < prv_nodeInfos.size(); i++)
    // {
    //     // std::cout << "RENAMING " << std::endl << nodeInfos[i].node << std::endl;
    //     Node renamed = rename(prv_nodeInfos[i].node, freeVar2node, boundVar2node, nodeManager);
    //     // std::cout << "RENAMED " << std::endl << renamed << std::endl;
    //     nodeInfos.push_back(getNodeInfo(renamed));
    //     // std::cout << "---------------------------------" << std::endl;
    // }

    */


    


    for (size_t i = 0; i < nodeInfos.size(); i++)
    {
        assertionsToPreprocess->replace(i, nodeInfos[i].node);
        // std::cout << nodeInfos[i].node << std::endl;
    }




  return PreprocessingPassResult::NO_CONFLICT;
}


Daneshvar::Statistics::Statistics(StatisticsRegistry& reg)
    : d_passTime(reg.registerTimer("Daneshvar::pass_time"))
{
}




}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal