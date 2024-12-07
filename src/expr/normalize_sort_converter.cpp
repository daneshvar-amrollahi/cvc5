/*
 * Implementation file for NormalizeSortNodeConverter
 */

#include "expr/normalize_sort_converter.h"

namespace cvc5::internal {

NormalizeSortNodeConverter::NormalizeSortNodeConverter(const std::map<TypeNode, TypeNode>& normalizedSorts)
    : NodeConverter(), d_normalizedSorts(normalizedSorts)
{
}

TypeNode NormalizeSortNodeConverter::postConvertType(TypeNode tn)
{
  auto it = d_normalizedSorts.find(tn);
  if (it != d_normalizedSorts.end())
  {
    return it->second;
  }
  return tn;
}

}  // namespace cvc5::internal
