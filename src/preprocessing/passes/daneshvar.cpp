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
    std::vector<int> varSeq;
    std::vector<std::string> varNames; 
    NodeInfo(Node n, std::string e, std::vector<int> vs, std::vector<std::string> vn) : node(n), encoding(e), varSeq(vs), varNames(vn) {}
};

NodeInfo getNodeInfo(Node n)
{
    std::string encoding = "";
    std::vector<std::string> varNames; 
    dfs(n, encoding, varNames);
    encoding += "\n";

    std::vector<int> varSeq;
    std::map<std::string, int> varMap;
    int id = 1;
    for (size_t i = 0; i < varNames.size(); ++i)
    {
        if (varMap.find(varNames[i]) == varMap.end())
        {
            varMap[varNames[i]] = id++;
        }
        varSeq.push_back(varMap[varNames[i]]);
    }
    return NodeInfo(n, encoding, varSeq, varNames);
}


bool nodeInfoCmp(const NodeInfo& a, const NodeInfo& b)
{
    if (a.encoding == b.encoding)
    {
        AssertArgument(a.varSeq.size() == b.varSeq.size(), a.toString() + " and " + b.toString() + " have the same encoding but different variable sequence size");
        size_t n = a.varSeq.size();
        for (size_t i = 0; i < n; i++)
        {
            if (a.varSeq[i] != b.varSeq[i])
            {
                return a.varSeq[i] < b.varSeq[i];
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
        return false;
    }
    return a.encoding < b.encoding;
}

bool operandsCmpR2(const Node& a, const Node& b)
{
    std::string sa, sb;
    if (a.isVar() || a.isConst())
    {
        sa = a.toString();
    }
    else
    {
        cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(a.getKind());
        sa = cvc5::internal::kind::toString(k);
    }

    if (b.isVar() || b.isConst())
    {
        sb = b.toString();
    }
    else
    {
        cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(b.getKind());
        sb = cvc5::internal::kind::toString(k);
    }
    return sa < sb;
}


bool operandsCmpR1(const Node& a, const Node& b)
{
    std::string sa, sb;
    if (a.isVar())
    {
        sa = "V";
    }
    else if (a.isConst())
    {
        sa = a.toString();
    }
    else
    {
        cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(a.getKind());
        sa = cvc5::internal::kind::toString(k);
    }

    if (b.isVar())
    {
        sb = "V";
    } 
    else if (b.isConst())
    {
        sb = b.toString();
    }
    else
    {
        cvc5::internal::Kind k = static_cast<cvc5::internal::Kind>(b.getKind());
        sb = cvc5::internal::kind::toString(k);
    }
    return sa < sb;
}


std::pair<std::string, std::string> getFirstDiffVars(const std::vector<std::string> &a, const std::vector<std::string> &b)
{
    int n = std::min(a.size(), b.size());
    for (int i = 0; i < n; i++)
    {
        if (a[i] != b[i])
        {
            return std::make_pair(a[i], b[i]);
        }
    }
    return std::make_pair("", ""); // ToDo: Add assertion failed
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

Node sortOp(Node n, int round)
{
    // Sort the operands of each operator using the variable names
    if (n.isVar() || n.isConst())
    {
        return n;
    }
    std::vector<Node> operands;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        operands.push_back(sortOp(n[i], round));
    } 
    int commutative = isCommutative(n.getKind());


    if (commutative == 0)
    {
        std::sort(operands.begin(), operands.end(), round == 1 ? operandsCmpR1 : operandsCmpR2);

    } else if (commutative == 1)
    {
        std::sort(operands.begin() + 1, operands.end(), round == 1 ? operandsCmpR1 : operandsCmpR2);
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


Node rename(
    Node n, 
    std::map<std::string, Node> &freeVar2node, 
    std::map<std::string, Node> &boundVar2node, 
    NodeManager* nodeManager, 
    bool insideQuantifierBody = false)
{
    // std::cout << "Renaming " << n << std::endl;
    if (n.isConst())
    {
        return n;
    }
    if (n.isVar())
    {
        if (n.getKind() == cvc5::internal::Kind::BOUND_VARIABLE)
        {
            if (boundVar2node.find(n.toString()) != boundVar2node.end())
            {
                return boundVar2node[n.toString()];
            }
            else
            {
                int id = boundVar2node.size() + 1;
                Node ret = nodeManager->mkBoundVar("v" + std::to_string(id), n.getType());
                boundVar2node[n.toString()] = ret;
                return ret;
            }
        }
        else
        {
            if (freeVar2node.find(n.toString()) != freeVar2node.end())
            {
                return freeVar2node[n.toString()];
            }
            else
            {
                std::vector<Node> cnodes;
                int id = freeVar2node.size();
                cnodes.push_back(nodeManager->mkConst(String("v" + std::to_string(id), false)));
                Node gt = nodeManager->mkConst(SortToTerm(n.getType()));
                cnodes.push_back(gt);
                Node ret = nodeManager->getSkolemManager()->mkSkolemFunction(SkolemFunId::INPUT_VARIABLE, cnodes);
                freeVar2node[n.toString()] = ret;
                return ret;
            }
        }

    }

    std::vector<Node> children;
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
        children.push_back(n.getOperator());
    }
    
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        children.push_back(rename(n[i], freeVar2node, boundVar2node, nodeManager));
    }

    // std::cout << freeVar2node.size() << " " << boundVar2node.size() << std::endl;

    if (n.getKind() == cvc5::internal::Kind::FORALL || n.getKind() == cvc5::internal::Kind::EXISTS)
    {
        Node bound_vars = n[0];
        // std::cout << "BOUND_VAR_LIST" << std::endl;
        for (size_t i = 0; i < bound_vars.getNumChildren(); i++)
        {
            // std::cout << "Erasing " << bound_vars[i].toString() << ":" << boundVar2node[bound_vars[i].toString()] << std::endl;
            AssertArgument(boundVar2node.find(bound_vars[i].toString()) != boundVar2node.end(), "Bound variable not found in boundVar2node");
            boundVar2node.erase(bound_vars[i].toString());
        }
    }


    
    return nodeManager->mkNode(n.getKind(), children);
}



PreprocessingPassResult Daneshvar::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    TimerStat::CodeTimer codeTimer(d_statistics.d_passTime);

    /////////////////////////////////////////////////////////////
    // Step 1: Fix anti-symmetric operators
    std::vector <Node> assertions;
    for (const Node& assertion : assertionsToPreprocess->ref())
    {
        assertions.push_back(fixflips(assertion));
    }

    // std::cout << "After fix flips:" << std::endl;
    // for (size_t i = 0; i < assertions.size(); ++i)
    // {
    //     std::cout << assertions[i] << std::endl;
    // }

    /////////////////////////////////////////////////////////////
    // Step 2: Sort operands of commutative operators
    for (size_t i = 0; i < assertions.size(); ++i)
    {
        assertions[i] = sortOp(assertions[i], 1);
    }




    /////////////////////////////////////////////////////////////
    // Step 3: Sort the assertions based on their encoding
    std::vector<NodeInfo> nodeInfos;
    for (size_t i = 0; i < assertions.size(); ++i)
    {
        nodeInfos.push_back(getNodeInfo(assertions[i]));
    }   

    sort(nodeInfos.begin(), nodeInfos.end(), nodeInfoCmp);

    std::cout << "After sorting:" << std::endl;
    for (size_t i = 0; i < nodeInfos.size(); i++)
    {
        std::cout << nodeInfos[i].node << std::endl;
        // std::cout << nodeInfos[i].encoding << std::endl;
        // std::vector<int> varSeq = nodeInfos[i].varSeq;
        // // for (size_t j = 0; j < varSeq.size(); j++)
        // // {
        // //     std::cout << varSeq[j] << " ";
        // // }
        // std::cout << std::endl;
        // std::cout << "----" << std::endl;
    }

    std::cout << "---------------------------------" << std::endl;

    /////////////////////////////////////////////////////////////
    // Step 4: Variable normalization
    std::map<std::string, Node> freeVar2node;
    std::map<std::string, Node> boundVar2node;
    NodeManager* nodeManager = NodeManager::currentNM();
    std::cout << "After renaming:" << std::endl;
    for (size_t i = 0; i < nodeInfos.size(); i++)
    {
        // std::cout << "RENAMING " << nodeInfos[i].node << std::endl;
        Node renamed = rename(nodeInfos[i].node, freeVar2node, boundVar2node, nodeManager);
        nodeInfos[i].node = renamed;
        // std::cout << "RENAMED " << renamed << std::endl;
        // std::cout << "---------------------------------" << std::endl;
        std::cout << renamed << std::endl;
    }

    abort();


    /////////////////////////////////////////////////////////////
    // Step 5: Sort operands of commutative operators

    for (size_t i = 0; i < nodeInfos.size(); i++)
    {
        Node reordered = sortOp(nodeInfos[i].node, 2);
        nodeInfos[i] = getNodeInfo(reordered);
    }


    /////////////////////////////////////////////////////////////
    // Step 6: Final sort
    sort(nodeInfos.begin(), nodeInfos.end(), nodeInfoCmp); 



    /////////////////////////////////////////////////////////////
    // Step 5: Final renaming
    // freeVar2node.clear();
    // boundVar2node.clear();
    // for (size_t i = 0; i < nodeInfos.size(); i++)
    // {
    //     std::cout << "RENAMING " << std::endl << nodeInfos[i].node << std::endl;
    //     Node renamed = rename(nodeInfos[i].node, freeVar2node, boundVar2node, nodeManager);
    //     std::cout << "RENAMED " << std::endl << renamed << std::endl;
    //     nodeInfos[i] = getNodeInfo(renamed);
    //     std::cout << "---------------------------------" << std::endl;
    // }

    for (size_t i = 0; i < nodeInfos.size(); i++)
    {
        assertionsToPreprocess->replace(i, nodeInfos[i].node);
        std::cout << nodeInfos[i].node << std::endl;
    }

    abort();
    
    // std::cout << "Current logic is " << d_env.getLogicInfo().getLogicString() << std::endl;

    // const std::vector<Node>& assertions = assertionsToPreprocess->ref();

    // std::vector <vertex> nodes;
    // for (const Node& assertion : assertions)
    // {
    //     nodes.push_back(getVertex(assertion));
    // }

    // sort(nodes.begin(), nodes.end(), assertionsCmp);


    // // std::cout << "After sorting:" << std::endl;
    // // for (size_t i = 0; i < nodes.size(); i++)
    // // {
    // //     std::cout << nodes[i].node << std::endl;
    // //     std::cout << nodes[i].encoding << std::endl;
    // //     std::cout << "----" << std::endl;
    // // }
    // // std::cout << "---------------------------------" << std::endl;

        
    // // VARIABLE NORMALIZATION

    // // Map variables to integers
    // std::map<std::string, unsigned> varMap;
    // unsigned id = 1;
    // for (size_t i = 0; i < nodes.size(); i++)
    // {
    //     for (size_t j = 0; j < nodes[i].varNames.size(); j++)
    //     {
    //         if (varMap.find(nodes[i].varNames[j]) == varMap.end())
    //         {
    //             varMap[nodes[i].varNames[j]] = id++;
    //             // std::cout << "Mapped " << nodes[i].varNames[j] << " to " << varMap[nodes[i].varNames[j]] << std::endl;
    //         }
    //     }
    // }
    
    // // std::cout << std::endl;

    // // Construct dependency graph
    // for (size_t i = 0; i < nodes.size(); i++)
    // {
    //     for (size_t j = 0; j < i; j++)
    //     {
    //         if (nodes[i].encoding == nodes[j].encoding)
    //         {
    //             std::pair<std::string, std::string> diffVars = getFirstDiffVars(nodes[j].varNames, nodes[i].varNames);
    //             std::string var_j = diffVars.first;
    //             std::string var_i = diffVars.second;
    //             int vj = varMap[var_j], vi = varMap[var_i];
    //             // std::cout << "Edge " << var_j << " -> " << var_i << std::endl;
    //             adj[vj].push_back(vi);
    //         }
    //     }
    // }

    // // Topological sort
    // std::stack<int> st;
    // std::vector<bool> mark(id + 1, false);
    // for (size_t i = 1; i < id; i++)
    // {
    //     if (!mark[i])
    //     {
    //         topolsort(i, mark, st);
    //     }
    // }

    // // Assign new names (v_counter) to variables based on topological order
    // std::map<int, int> normVar;
    // unsigned counter = 1;
    // while (!st.empty())
    // {
    //     int v = st.top();
    //     st.pop();
    //     normVar[v] = counter++;
    //     // std::cout << "Renamed " << v << " to v" << normVar[v] << std::endl;
    // }


    // // Rebuild the assertions
    // // std::cout << "End of pass:" << std::endl;
    // NodeManager* nodeManager = NodeManager::currentNM();
    // for (size_t i = 0; i < nodes.size(); i++)
    // {
    //     // std::cout << "Before pass:" << std::endl;
    //     // std::cout << nodes[i].node << std::endl;
    //     Node renamed = normalize(nodes[i].node, normVar, varMap, nodeManager);          // normalize symbol names
    //     // std::cout << "Renamed " << renamed << std::endl;
    //     Node reordered = reorder(renamed);                                              // sort the operands of each commutative operator using the variable names
    //     // std::cout << "Reordered " << reordered << std::endl;
    //     Node flipped = fixflips(reordered);                                             // fix the flips
    //     // std::cout << "After pass:" << std::endl;
    //     // std::cout << flipped << std::endl;
    //     // std::cout << "---------------------------------" << std::endl;
    //     assertionsToPreprocess->replace(i, flipped);
    // }


    // exit(0);
    

  return PreprocessingPassResult::NO_CONFLICT;
}


Daneshvar::Statistics::Statistics(StatisticsRegistry& reg)
    : d_passTime(reg.registerTimer("Daneshvar::pass_time"))
{
}




}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
