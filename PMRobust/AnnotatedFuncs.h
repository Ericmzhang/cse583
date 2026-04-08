#ifndef ANNOTATED_FUNCS_H
#define ANNOTATED_FUNCS_H
#include <stdlib.h>

using NameAnno = std::pair<std::string, std::string>;

static const NameAnno AnnotatedFuncs[] = { NameAnno{"read", "persist_memcpy:ignore|addr|size"} };

#endif
