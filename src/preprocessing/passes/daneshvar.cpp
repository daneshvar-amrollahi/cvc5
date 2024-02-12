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
    std::vector<std::string> varNames;
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

    std::cout << "Assertions after daneshvar pass" << std::endl;
    for (size_t i = 0; i < nodes.size(); i++)
    {
        std::cout << nodes[i].node << std::endl;
        std::cout << nodes[i].encoding << std::endl;
        std::cout << "--------------" << std::endl;
    }

    for (size_t i = 0; i < assertionsToPreprocess->size(); ++i)
    {
        assertionsToPreprocess->replace(i, nodes[i].node);
    }
    
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
