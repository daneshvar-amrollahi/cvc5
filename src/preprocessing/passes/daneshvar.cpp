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

void dfs(Node n, std::string& encoding, std::vector<std::string> &varNames)
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


struct NodeInfo
{
    Node node;
    std::string encoding;
    std::vector<int> pat;
    std::vector<std::string> varNames; 
    std::map<std::string, int> role;
    unsigned equivClassId_ass;
    unsigned equivClassId_operands; 
    NodeInfo() {
        
    }
    NodeInfo(Node n, std::string e, std::vector<int> p, std::vector<std::string> vn, std::map<std::string, int> r, unsigned ecId_ass, unsigned ecId_op) : 
        node(n), encoding(e), pat(p), varNames(vn), role(r), equivClassId_ass(ecId_ass), equivClassId_operands(ecId_op) {}
};

std::map<int, std::vector<NodeInfo>> ec_ass;
std::map<int, std::vector<NodeInfo>> ec_oper;

int getRole(std::string var, NodeInfo n)
{
    if (n.role.find(var) != n.role.end())
    {
        return n.role[var];
    }
    return 0;
}

NodeInfo getNodeInfo(Node n, unsigned ecId_ass, unsigned ecId_op)
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

bool operandsCmpR2(const Node& a, const Node& b)
{
    // std::cout << "Comparing " << a << " and " << b << std::endl;
    std::string sa, sb;
    if (a.isVar() || a.isConst())
    {
        sa = a.toString();
    }
    else
    {
        // cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(a.getKind());
        // sa = cvc5::internal::kind::toString(k);
        sa = a.toString();
    }

    if (b.isVar() || b.isConst())
    {
        sb = b.toString();
    }
    else
    {
        // cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(b.getKind());
        // sb = cvc5::internal::kind::toString(k);
        sb = b.toString();
    }
    // std::cout << "sa=" << sa << ", sb=" << sb << std::endl;
    // std::cout << "*****" << std::endl;
    return sa < sb;
}


bool operandsCmpR1(const NodeInfo& nia, const NodeInfo& nib)
{
    // std::cout << "Comparing " << nia.node << " and " << nib.node << std::endl;
    Node a = nia.node, b = nib.node;
    // std::string sa, sb;
    // if (a.isVar())
    // {
    //     sa = "V";
    // }
    // else if (a.isConst())
    // {
    //     sa = a.toString();
    // }
    // else
    // {
    //     cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(a.getKind());
    //     sa = cvc5::internal::kind::toString(k);
    // }

    // if (b.isVar())
    // {
    //     sb = "V";
    // } 
    // else if (b.isConst())
    // {
    //     sb = b.toString();
    // }
    // else
    // {
    //     cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(b.getKind());
    //     sb = cvc5::internal::kind::toString(k);
    // }
    // if (sa != sb)
    // {
    //     return sa < sb;
    // }
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
    for (int i = 0; i < nia.varNames.size(); ++i)
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




bool operandsCmpR3(const NodeInfo& nia, const NodeInfo& nib)
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

    // Calculate super-pattern of diff pairs of variables in the next equivalent classes of OPERANDS and compare them

    for (int i = 0; i < nia.varNames.size(); ++i)
    {
        if (nia.varNames[i] == nib.varNames[i])
        {
            continue;
        }
        std::string var_a = nia.varNames[i], var_b = nib.varNames[i]; // first different variables in a and b
        
        int ecId_oper = nia.equivClassId_operands; // = b.equivClassId_operands
        std::vector<int> spat_a, spat_b;
        for (int j = ecId_oper; ec_oper[j].size() > 0; ++j)
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




    // Calculate super-pattern of diff pairs of variables in the next equivalent classes of ASSERTIONS and compare them
    

    for (int i = 0; i < nia.varNames.size(); ++i)
    {
        if (nia.varNames[i] == nib.varNames[i])
        {
            continue;
        }
        std::string var_a = nia.varNames[i], var_b = nib.varNames[i]; // first different variables in a and b

        int ecId_ass = nia.equivClassId_ass; // = b.equivClassId_ass
        std::vector<int> spat_a, spat_b;
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
            // Append pattern of var_a in ec_ass[j] to spat_a
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

    // Should we not care at this point? Only Clark knows. 
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

bool complexCmp(const NodeInfo& a, const NodeInfo& b)
{
    if (a.equivClassId_ass  != b.equivClassId_ass)
    {
        return a.equivClassId_ass < b.equivClassId_ass;
    }


    // a and b belong to the same class

    // Calculate super-pattern of diff pairs of variables in the next equivalent classes and compare them
    int ecId_ass = a.equivClassId_ass; // also b.equivClassId_ass
    std::vector<int> spat_a, spat_b;
    for (int i = 0; i < a.varNames.size(); ++i)
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

            // std::cout << "j=" << j << std::endl;
            // std::cout << "pat_a: ";
            // for (size_t k = 0; k < pat_j_a.size(); k++)
            // {
            //     std::cout << pat_j_a[k] << " ";
            // }
            // std::cout << std::endl;
            // std::cout << "pat_b: ";
            // for (size_t k = 0; k < pat_j_b.size(); k++)
            // {
            //     std::cout << pat_j_b[k] << " ";
            // }
            // std::cout << std::endl;

            sort(pat_j_a.begin(), pat_j_a.end());
            sort(pat_j_b.begin(), pat_j_b.end());
            // Append pattern of var_a in ec_ass[j] to spat_a
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

    // std::cout << "Super-patterns are the same for " << a.node << " and " << b.node << std::endl;
    // for (size_t i = 0; i < spat_a.size(); i++)
    // {
    //     std::cout << spat_a[i] << " ";
    // }
    // std::cout << std::endl;
    // for (size_t i = 0; i < spat_b.size(); i++)
    // {
    //     std::cout << spat_b[i] << " ";
    // }
    // std::cout << std::endl;

    // What happens here?
    return false;   
}



// Return vector index >= 0 (from where the list of children is commutative)
// if true, else -1.
int isCommutative(cvc5::internal::Kind k)
{
    if (k == cvc5::internal::Kind::ADD) // ToDo: Other than arithmetic?
        return 0;
    if (k == cvc5::internal::Kind::MULT) // ToDo: Other than arithmetic?
        return 0;
    if (k == cvc5::internal::Kind::AND)
        return 0;
    if (k == cvc5::internal::Kind::OR)
        return 0;
    if (k == cvc5::internal::Kind::XOR)
        return 0;
    if (k == cvc5::internal::Kind::DISTINCT)
        return 0;
    if (k == cvc5::internal::Kind::EQUAL) // ToDo: How about difference logic
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

bool sameClass(NodeInfo a, NodeInfo b)
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


Node sortOp1(NodeInfo ni)
{
    Node n = ni.node;
    if (n.isVar() || n.isConst())
    {
        return n;
    }
    std::vector<NodeInfo> child;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        child.push_back(getNodeInfo(sortOp1(getNodeInfo(n[i], -1, -1)), -1, -1));
    } 
    int commutative = isCommutative(n.getKind());


    if (commutative != -1)
    {

        // Calculate equivalence classes for the children (operands)
        ec_oper.clear();
        std::sort(child.begin() + commutative, child.end(), equivClassCalcCmp);

        int ecId_operands = 1;
        child[commutative].equivClassId_operands = ecId_operands;
        ec_oper[ecId_operands].push_back(child[commutative]);
        for (size_t i = commutative + 1; i < child.size(); i++)
        {
            if (!sameClass(child[i], child[i - 1]))
            {
                ecId_operands++;
            }
            child[i].equivClassId_operands = ecId_operands;
            ec_oper[ecId_operands].push_back(child[i]);
        }

        std::sort(child.begin(), child.begin() + commutative, operandsCmpR1);

    }



    std::vector<Node> operands;
    for (size_t i = 0; i < child.size(); i++)
    {
        operands.push_back(child[i].node);
    }

    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
        operands.insert(operands.begin(), n.getOperator());
    }


    return NodeManager::currentNM()->mkNode(n.getKind(), operands);   
}



Node sortOperands(NodeInfo ni) {
    Node n = ni.node;
    if (n.isVar() || n.isConst()) {
        return n;
    }

    // Two stacks for the DFS traversal
    std::stack<NodeInfo> toVisit;
    std::stack<NodeInfo> processStack;

    toVisit.push(ni);

    // Stores the child nodes for each node to be processed later
    std::map<Node, std::vector<NodeInfo>> nodeChildrenMap;

    while (!toVisit.empty()) {
        NodeInfo currentNodeInfo = toVisit.top();
        toVisit.pop();

        Node currentNode = currentNodeInfo.node;

        if (currentNode.isVar() || currentNode.isConst()) {
            continue;
        }

        processStack.push(currentNodeInfo);

        std::vector<NodeInfo> child;
        for (size_t i = 0; i < currentNode.getNumChildren(); i++) {
            NodeInfo childInfo = getNodeInfo(currentNode[i], -1, -1);
            child.push_back(childInfo);
            toVisit.push(childInfo);
        }
        nodeChildrenMap[currentNode] = child;
    }

    // Now process the nodes in the correct order
    while (!processStack.empty()) {
        NodeInfo currentNodeInfo = processStack.top();
        processStack.pop();

        Node currentNode = currentNodeInfo.node;
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

            std::sort(child.begin(), child.begin() + commutative, operandsCmpR1);
        }

        std::vector<Node> operands;
        for (size_t i = 0; i < child.size(); i++) {
            operands.push_back(child[i].node);
        }

        if (currentNode.getMetaKind() == metakind::PARAMETERIZED) {
            operands.insert(operands.begin(), currentNode.getOperator());
        }

        Node sortedNode = NodeManager::currentNM()->mkNode(currentNode.getKind(), operands);
        nodeChildrenMap[currentNode] = { getNodeInfo(sortedNode, -1, -1) };
    }

    return nodeChildrenMap[n][0].node;
}




Node sortOp3(NodeInfo ni)
{
    Node n = ni.node;
    if (n.isVar() || n.isConst())
    {
        return n;
    }
    std::vector<NodeInfo> child;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        int ecId_ass = ni.equivClassId_ass;
        NodeInfo curr = getNodeInfo(n[i], ecId_ass, -1);
        child.push_back(getNodeInfo(sortOp3(curr), ecId_ass, -1));
    } 
    int commutative = isCommutative(n.getKind());


      
    if (commutative != -1)
    {
        // Calculate equivalence classes for the children (operands)
        ec_oper.clear();
        std::sort(child.begin() + commutative, child.end(), equivClassCalcCmp);

        int ecId_operands = 1;
        child[commutative].equivClassId_operands = ecId_operands;
        ec_oper[ecId_operands].push_back(child[commutative]);
        for (size_t i = commutative + 1; i < child.size(); i++)
        {
            if (!sameClass(child[i], child[i - 1]))
            {
                ecId_operands++;
            }
            child[i].equivClassId_operands = ecId_operands;
            ec_oper[ecId_operands].push_back(child[i]);
        }

        std::sort(child.begin() + commutative, child.end(), operandsCmpR3);
    }



    std::vector<Node> operands;
    for (size_t i = 0; i < child.size(); i++)
    {
        operands.push_back(child[i].node);
    }

    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
        operands.insert(operands.begin(), n.getOperator());
    }


    return NodeManager::currentNM()->mkNode(n.getKind(), operands);   

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





Node rename(
    Node n, 
    std::map<std::string, Node> &freeVar2node, 
    std::map<std::string, Node> &boundVar2node, 
    NodeManager* nodeManager)
{
    std::map<Node, Node> normalized;
    std::stack<Node> stack1, stack2;
    
    stack1.push(n);

    while (!stack1.empty()) {
        Node current = stack1.top();
        stack1.pop();
        stack2.push(current);

        if (current.isConst() || current.isVar()) {
            continue;
        }

        if (current.getKind() == cvc5::internal::Kind::APPLY_UF) {
            stack1.push(current.getOperator());
        } else if (current.getMetaKind() == metakind::PARAMETERIZED) {
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
                if (boundVar2node.find(current.toString()) != boundVar2node.end()) {
                    normalized[current] = boundVar2node[current.toString()];
                } else {
                    int id = boundVar2node.size();
                    std::string new_var_name = "u";
                    for (int i = 0; i < 5 - numDigits(id); i++) {
                        new_var_name += "0";
                    }
                    new_var_name += std::to_string(id);
                    Node ret = nodeManager->mkBoundVar(new_var_name, current.getType());
                    boundVar2node[current.toString()] = ret;
                    normalized[current] = ret;
                }
            } else {
                if (freeVar2node.find(current.toString()) != freeVar2node.end()) {
                    normalized[current] = freeVar2node[current.toString()];
                } else {
                    std::vector<Node> cnodes;
                    int id = freeVar2node.size();
                    std::string new_var_name = "v";
                    for (int i = 0; i < 5 - numDigits(id); i++) {
                        new_var_name += "0";
                    }
                    new_var_name += std::to_string(id);
                    cnodes.push_back(nodeManager->mkConst(String(new_var_name, false)));
                    Node gt = nodeManager->mkConst(SortToTerm(current.getType()));
                    cnodes.push_back(gt);
                    Node ret = nodeManager->getSkolemManager()->mkSkolemFunction(SkolemFunId::INPUT_VARIABLE, cnodes);
                    freeVar2node[current.toString()] = ret;
                    normalized[current] = ret;
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
            for (size_t i = 0; i < bound_vars.getNumChildren(); i++) {
                AssertArgument(boundVar2node.find(bound_vars[i].toString()) != boundVar2node.end(), "Bound variable not found in boundVar2node");
                boundVar2node.erase(bound_vars[i].toString());
            }
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
        Node curr = sortOperands(ni);
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
    ec_ass[ecId_ass].push_back(nodeInfos[0]);
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
        ec_ass[ecId_ass].push_back(nodeInfos[i]);
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
    sort(nodeInfos.begin(), nodeInfos.end(), complexCmp);
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
        Node renamed = rename(ni.node, freeVar2node, boundVar2node, nodeManager);
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
    //     std::cout << nodeInfos[i].node << std::endl;
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