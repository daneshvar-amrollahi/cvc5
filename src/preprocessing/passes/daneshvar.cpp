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

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Daneshvar::Daneshvar(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "daneshvar"){};



unsigned getDAGSize(Node n, std::map<Node, bool>& visited)
{
    visited[n] = true;
    if (n.isVar() || n.isConst())
    {
        return 1;
    }
    unsigned size = 1;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        if (visited.find(n[i]) == visited.end())
        {
            size += getDAGSize(n[i], visited);
        }
    }
    return size;
}

PreprocessingPassResult Daneshvar::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    // std::cout << "Executing pass daneshvar" << std::endl;

    const std::vector<Node>& assertions = assertionsToPreprocess->ref();
    std::vector<std::pair<Node, unsigned>> nodes;
    std::map<Node, bool> visited;
    for (const Node& assertion : assertions)
    {
        visited.clear();
        unsigned size = getDAGSize(assertion, visited);
        nodes.push_back(std::make_pair(assertion, size));
    }

    sort(nodes.begin(), nodes.end(), [](const std::pair<Node, unsigned>& a, const std::pair<Node, unsigned>& b) {
        return a.second < b.second;
    });

    for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
    {
        assertionsToPreprocess->replace(i, nodes[i].first);
    }
    


    // std::cout << "Assertions after sorting: " << std::endl;
    // for (const auto& node : assertionsToPreprocess->ref())
    // {
    //     std::cout << node << std::endl;
    // }

    // std::cout << "Finished pass daneshvar" << std::endl;


  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
