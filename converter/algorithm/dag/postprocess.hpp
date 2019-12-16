#ifndef _DAG_HPP
#define _DAG_POSTPROCESS_HPP 1

#include "dag.hpp"

bool check_indegree_one_alg(dag *d)
{
    bool all_correct = true;
    for (auto const & [key, v] : alg_by_hash)
    {
	if (v->in.size() != 1)
	{
	    all_correct = false;
	}
    }

    return all_correct;
}

// Remove all duplicate vertices that were different in the lower bound search,
// but are currently equivalent.
// Example: A = [6,5,0] [last:5] {0,0,0,0,1,1}
//          B = [6,5,0] [last:6] {0,0,0,0,1,1}
// They can be evaluated differently in the lower bound search, but if both are winning for the same player,
// they are the same.

using multiit = std::multimap<uint64_t, adversary_vertex*>::iterator;

void postprocess_merge_equals(dag *d)
{
    // Create a multimap of all adversary vertices
    std::multimap<uint64_t, adversary_vertex *> adv_by_loaditemhash;

    for ( const auto & [hash, vert] : adv_by_id)
    {
	adv_by_loaditemhash.insert(std::make_pair(vert->bc.loaditemhash(), vert));
    }


    // Create beginnings of new equivalence classes;
    std::vector<multiit> eq;
    for( multiit it = adv_by_loaditemhash.begin(), end = adv_by_loaditemhash.end(); it != end;
	  it = adv_by_loaditemhash.upper_bound(it->first))
    {
	eq.push_back(it);
    }

    for (int i = 0; < eq.size(); i++)
    {
    }
    
}

#endif
