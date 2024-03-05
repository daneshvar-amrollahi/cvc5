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


bool cmp(const vertex& a, const vertex& b)
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

Node renameVariables(Node n, unsigned int &counter, std::map<std::string, unsigned int> &varMap, NodeManager* nodeManager)
{
    if (n.isVar())
    {
        std::string varname = n.toString();
        if (varMap.find(varname) == varMap.end())
        {
            varMap[varname] = counter++;
            // std::cout << "Variable " << varname << " is renamed to " << "v" + std::to_string(varMap[n]) << std::endl;
        }

        // Approach 1 (Fresh Variables): Crashing + not allowed
        // return NodeManager::currentNM()->mkVar("v" + std::to_string(varMap[n]), n.getType());

        // Approach 2 (Fresh variables): sat instead of unsat
        // Node node = NodeBuilder(nodeManager , Kind::VARIABLE);
        // nodeManager->setAttribute(node, cvc5::internal::expr::TypeAttr(), n.getType());
        // nodeManager->setAttribute(node, cvc5::internal::expr::TypeCheckedAttr(), true);
        // nodeManager->setAttribute(node, expr::VarNameAttr(), "v" + std::to_string(varMap[n]));
        // return node;


        // Node pnode = nodeManager->getSkolemManager()->mkPurifySkolem(n);

        // Approach 3 (Non Fresh Variables): Crashing
        std::vector<Node> cnodes;
        cnodes.push_back(nodeManager->mkConst(String("v" + std::to_string(varMap[varname]), false)));
        // Since we index only on Node, we must construct a SortToTerm here.
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
        children.push_back(renameVariables(n[i], counter, varMap, nodeManager));
    }

    if (n.hasOperator())
    {
        Node op = n.getOperator();
        return nodeManager->mkNode(op, children);
    }

    return nodeManager->mkNode(n.getKind(), children);
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


Node rebuild(Node n, std::map<int, int> &normVar, std::map<std::string, unsigned> &varMap, NodeManager* nodeManager)
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
        children.push_back(rebuild(n[i], normVar, varMap, nodeManager));
    }

    if (n.hasOperator())
    {
        Node op = n.getOperator();
        return nodeManager->mkNode(op, children);
    }

    return nodeManager->mkNode(n.getKind(), children);
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

    sort(nodes.begin(), nodes.end(), cmp);

    

    
    // //No variable normalization 
    // for (size_t i = 0; i < assertionsToPreprocess->size(); ++i)
    // {
    //     assertionsToPreprocess->replace(i, nodes[i].node);
    // }
    

   

    // /*
    // Variable normalization 1.0
    // unsigned int id = 1; // counter for renaming variables
    // std::map<Node, unsigned int> varMap; // map from variable to its new name
    // NodeManager* nodeManager = NodeManager::currentNM();
    // for (size_t i = 0; i < nodes.size(); i++)
    // {
    //     // std::cout << nodes[i].node << std::endl;
    //     // std::cout << nodes[i].encoding << std::endl;
    //     // std::cout << "Before renaming: " << std::endl << nodes[i].node << std::endl;
    //     Node renamed = renameVariables(nodes[i].node, id, varMap, nodeManager);
    //     // std::cout << "After renaming: " << std::endl << renamed << std::endl;
    //     // std::cout << "--------------" << std::endl;
    //     assertionsToPreprocess->replace(i, renamed);
    // }
    // */
    
    
    // /*
    // Variable normalization 2.0
    // */
    
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
    // std::cout << std::endl << "Topological order: " << std::endl;
    std::map<int, int> normVar;
    unsigned counter = 1;
    while (!st.empty())
    {
        int v = st.top();
        st.pop();
        normVar[v] = counter++;
        // std::cout << "Assigned " << v << " to v" << normVar[v] << std::endl;
    }


    // Rebuild the assertions
    NodeManager* nodeManager = NodeManager::currentNM();
    // Co-pilot's suggestion. Using the RewriteRule instead of the SkolemManager?
    // for (size_t i = 0; i < nodes.size(); i++)
    // {
    //     Node renamed = nodes[i].node;
    //     for (size_t j = 0; j < nodes[i].varNames.size(); j++)
    //     {
    //         std::string varname = nodes[i].varNames[j];
    //         int v = varMap[varname];
    //         int newv = normVar[v];
    //         std::string newvarname = "v" + std::to_string(newv);
    //         Node oldvar = nodeManager->mkConst(String(varname, false));
    //         Node newvar = nodeManager->mkConst(String(newvarname, false));
    //         renamed = theory::Rewriter::rewrite(renamed.substitute(oldvar, newvar));
    //     }
    //     assertionsToPreprocess->replace(i, renamed);
    // }

    // std::cout << std::endl << " --------------- " << std::endl;
    for (size_t i = 0; i < nodes.size(); i++)
    {
        // std::cout << "Before renaming: " << std::endl << nodes[i].node << std::endl;
        Node renamed = rebuild(nodes[i].node, normVar, varMap, nodeManager);
        // std::cout << "After renaming: " << std::endl << renamed << std::endl;
        // std::cout << "--------------" << std::endl;
        assertionsToPreprocess->replace(i, renamed);
    }

    

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
