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

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Daneshvar::Daneshvar(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "daneshvar"){};

void dfs(Node n)
{
    std::cout << "Node: " << n << "   ";
    if (n.isVar() || n.isConst())
    {
        std::cout << "reached a leaf" << std::endl;
        return;
    }
    std::cout << std::endl;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
        dfs(n[i]);
    }
}

PreprocessingPassResult Daneshvar::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
    std::cout << "Executing pass daneshvar" << std::endl;

    const std::vector<Node>& assertions = assertionsToPreprocess->ref();

    for (const Node& assertion : assertions)
    {
        std::cout << "Assertion: " << assertion << std::endl;
        std::cout << "Calling dfs" << std::endl;
        dfs(assertion);
        std::cout << "*************" << std::endl;
        // std::cout << "Node kind: " << assertion.getKind() << std::endl;
        // std::cout << "Node type: " << assertion.getType() << std::endl;
        // std::cout << "Node num children: " << assertion.getNumChildren() << std::endl;
        // Node c0 = assertion[0];
        // Node c1 = assertion[1];
        // Node c2 = assertion[2];
        // std::cout << "Node 0: " << c0 << std::endl;
        // std::cout << "Node 1: " << c1 << std::endl;
        // std::cout << "Node 2: " << c2 << std::endl;
        // Node c20 = c2[0];
        // Node c21 = c2[1];
        // std::cout << "Node 20: " << c20 << " " << c20.getKind() << std::endl;
        // std::cout << "Node 21: " << c21 << " " << c21.getKind() << std::endl;

    }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
