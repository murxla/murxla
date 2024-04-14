/**
 * Murxla: A Model-Based API Fuzzer for SMT solvers.
 *
 * This file is part of Murxla.
 *
 * Copyright (C) 2019-2022 by the authors listed in the AUTHORS file.
 *
 * See LICENSE for more information on using this software.
 */

#include "sort.hpp"
#include <iostream>
#include <unordered_map>

namespace murxla {

// Define a hash map for quick lookup
static const std::unordered_map<std::string, SortKind> str_to_sort_kind = {
    {"INTEGER", SORT_INTEGER},
    {"REAL", SORT_REAL},
    {"BOOL", SORT_BOOL},
    // Add more mappings as needed
};

std::ostream& operator<<(std::ostream& out, SortKind kind) {
    out << sort_kinds_to_str.at(kind);
    return out;
}

bool operator==(const SortKindData& a, const SortKindData& b) {
    return (a.d_kind == b.d_kind && a.d_arity == b.d_arity && a.d_theory == b.d_theory);
}

SortKindSet get_all_sort_kinds_for_any(const SortKindSet& excluded_sorts) {
    SortKindSet res;
    for (uint32_t i = 0; i < SORT_ANY; ++i) {
        SortKind sort_kind = static_cast<SortKind>(i);
        if (excluded_sorts.find(sort_kind) == excluded_sorts.end()) {
            res.insert(sort_kind);
        }
    }
    return res;
}

SortKind sort_kind_from_str(const std::string& s) {
    auto it = str_to_sort_kind.find(s);
    if (it != str_to_sort_kind.end()) {
        return it->second;
    }
    return SORT_ANY;
}

} // namespace murxla

namespace std {

size_t hash<murxla::SortKind>::operator()(const murxla::SortKind& k) const {
    return k;
}

} // namespace std
