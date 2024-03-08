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

#include <map>
#include <stack>

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Daneshvar::Daneshvar(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "daneshvar"){};

void dfs(Node n, std::string& encoding, std::map<Node, bool> &visited, std::vector<std::string> &varNames)
{
    visited[n] = true;
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
    // std::cout << "kind of node " << n << std::endl <<  boz << std::endl;
    encoding += boz + ";";
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        if (!visited[n[i]])
        {
            dfs(n[i], encoding, visited, varNames);
        }
    }
}


struct vertex
{
    Node node;
    std::string encoding;
    std::vector<std::string> varNames;
    vertex(Node n, std::string e, std::vector<std::string> v) : node(n), encoding(e), varNames(v) {}
};

vertex getVertex(Node n)
{
    std::string encoding = "";
    std::map<Node, bool> visited;
    std::vector<std::string> varNames; // ToDo: change type to std::string?
    dfs(n, encoding, visited, varNames);
    encoding += "\n";
    return vertex(n, encoding, varNames);
}


bool assertionsCmp(const vertex& a, const vertex& b)
{
    if (a.encoding == b.encoding)
    {
        int n = std::min(a.varNames.size(), b.varNames.size());
        for (int i = 0; i < n; i++)
        {
            if (a.varNames[i] != b.varNames[i])
            {
                return a.varNames[i] < b.varNames[i];
            }
        }
        return a.varNames.size() < b.varNames.size();
    }
    return a.encoding < b.encoding;
}

bool operandsCmp(const Node& a, const Node& b)
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

const int maxN = 1e5 + 10; // Maximum number of variable names
std::vector<int> adj[maxN];

void topolsort(int v, std::vector<bool> &mark, std::stack<int> &st)
{
    mark[v] = true;
    for (int u : adj[v])
    {
        if (!mark[u])
        {
            topolsort(u, mark, st);
        }
    }
    st.push(v);
}


Node normalize(Node n, std::map<int, int> &normVar, std::map<std::string, unsigned> &varMap, NodeManager* nodeManager)
{
    if (n.isVar())
    {
        std::string varname = n.toString();
        int v = varMap[varname];
        int newv = normVar[v];
        
        std::vector<Node> cnodes;
        cnodes.push_back(nodeManager->mkConst(String("v" + std::to_string(newv), false)));
        Node gt = nodeManager->mkConst(SortToTerm(n.getType()));
        cnodes.push_back(gt);
        return nodeManager->getSkolemManager()->mkSkolemFunction(SkolemFunId::INPUT_VARIABLE, cnodes);
    }
    if (n.isConst())
    {
        return n;
    }
    std::vector<Node> children;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        children.push_back(normalize(n[i], normVar, varMap, nodeManager));
    }

    if (n.hasOperator())
    {
        Node op = n.getOperator();
        return nodeManager->mkNode(op, children);
    }

    return nodeManager->mkNode(n.getKind(), children);
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

Node reorder(Node n)
{
    // Sort the operands of each operator using the variable names
    if (n.isVar() || n.isConst())
    {
        return n;
    }
    std::vector<Node> operands;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        operands.push_back(reorder(n[i]));
    } 
    int commutative = isCommutative(n.getKind());


    if (commutative == 0)
    {
        std::sort(operands.begin(), operands.end(), operandsCmp);

    } else if (commutative == 1)
    {
        std::sort(operands.begin() + 1, operands.end(), operandsCmp);
    }

    if (n.hasOperator())
    {
        return NodeManager::currentNM()->mkNode(n.getOperator(), operands);
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
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        operands.push_back(fixflips(n[i]));
    }
    if (n.hasOperator())
    {
        return NodeManager::currentNM()->mkNode(n.getOperator(), operands);
    }
    return NodeManager::currentNM()->mkNode(n.getKind(), operands);
}

PreprocessingPassResult Daneshvar::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    const std::vector<Node>& assertions = assertionsToPreprocess->ref();

    std::vector <vertex> nodes;
    for (const Node& assertion : assertions)
    {
        nodes.push_back(getVertex(assertion));
    }

    sort(nodes.begin(), nodes.end(), assertionsCmp);


        
    // VARIABLE NORMALIZATION

    // Map variables to integers
    std::map<std::string, unsigned> varMap;
    unsigned id = 1;
    for (size_t i = 0; i < nodes.size(); i++)
    {
        for (size_t j = 0; j < nodes[i].varNames.size(); j++)
        {
            if (varMap.find(nodes[i].varNames[j]) == varMap.end())
            {
                varMap[nodes[i].varNames[j]] = id++;
                // std::cout << "Mapped " << nodes[i].varNames[j] << " to " << varMap[nodes[i].varNames[j]] << std::endl;
            }
        }
    }
    
    // std::cout << std::endl;

    // Construct dependency graph
    for (size_t i = 0; i < nodes.size(); i++)
    {
        for (size_t j = 0; j < i; j++)
        {
            if (nodes[i].encoding == nodes[j].encoding)
            {
                std::pair<std::string, std::string> diffVars = getFirstDiffVars(nodes[j].varNames, nodes[i].varNames);
                std::string var_j = diffVars.first;
                std::string var_i = diffVars.second;
                int vj = varMap[var_j], vi = varMap[var_i];
                // std::cout << "Edge " << vj << " -> " << vi << std::endl;
                adj[vj].push_back(vi);
            }
        }
    }

    // Topological sort
    std::stack<int> st;
    std::vector<bool> mark(id + 1, false);
    for (size_t i = 1; i < id; i++)
    {
        if (!mark[i])
        {
            topolsort(i, mark, st);
        }
    }

    // Assign new names (v_counter) to variables based on topological order
    std::map<int, int> normVar;
    unsigned counter = 1;
    while (!st.empty())
    {
        int v = st.top();
        st.pop();
        normVar[v] = counter++;
    }


    // Rebuild the assertions
    NodeManager* nodeManager = NodeManager::currentNM();
    for (size_t i = 0; i < nodes.size(); i++)
    {
        // std::cout << "Node " << i << " " << nodes[i].node << std::endl;
        Node renamed = normalize(nodes[i].node, normVar, varMap, nodeManager);          // normalize symbol names
        // std::cout << "Renamed " << renamed << std::endl;
        Node reordered = reorder(renamed);                                              // sort the operands of each commutative operator using the variable names
        // std::cout << "Reordered " << reordered << std::endl;
        Node flipped = fixflips(reordered);                                             // fix the flips
        // std::cout << "Flipped " << flipped << std::endl;
        // std::cout << "---------------------------------" << std::endl;
        assertionsToPreprocess->replace(i, renamed);
    }



    

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
