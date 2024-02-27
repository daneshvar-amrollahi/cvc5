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
#include <queue>

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
    std::vector<std::string> varNames; // ToDo: change to string
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

Node renameVariables(Node n, unsigned int &counter, std::map<Node, unsigned int> &varMap, NodeManager* nodeManager)
{
    if (n.isVar())
    {
        std::string varname = n.toString();
        if (varMap.find(n) == varMap.end())
        {
            varMap[n] = counter++;
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
        cnodes.push_back(nodeManager->mkConst(String("v" + std::to_string(varMap[n]), false)));
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

    // std::cout << "Assertions after daneshvar pass" << std::endl;
    unsigned int id = 1; // counter for renaming variables
    std::map<Node, unsigned int> varMap; // map from variable to its new name
    NodeManager* nodeManager = NodeManager::currentNM();
    for (size_t i = 0; i < nodes.size(); i++)
    {
        // std::cout << nodes[i].node << std::endl;
        // std::cout << nodes[i].encoding << std::endl;

        // std::cout << "Before renaming: " << std::endl << nodes[i].node << std::endl;
        Node renamed = renameVariables(nodes[i].node, id, varMap, nodeManager);
        // std::cout << "After renaming: " << std::endl << renamed << std::endl;
        // std::cout << "--------------" << std::endl;
        // std::cout << renamed << std::endl;
        assertionsToPreprocess->replace(i, renamed);
        // std::cout << "--------------" << std::endl;
    }

    // for (size_t i = 0; i < assertionsToPreprocess->size(); ++i)
    // {
    //     assertionsToPreprocess->replace(i, nodes[i].node);
    // }
    
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
