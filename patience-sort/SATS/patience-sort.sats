(*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

#define ATS_PACKNAME "ats2-patience-sort"
#define ATS_EXTERN_PREFIX "ats2_patience_sort_"

(* An index into the part of the input array to be sorted. *)
stadef patience_sort_index_t (ifirst : int, len : int, i : int) =
  len == 0 || (ifirst <= i && i < ifirst + len)
typedef patience_sort_index_t (tk : tkind, ifirst : int,
                               len : int, i : int) =
  [patience_sort_index_t (ifirst, len, i)]
  g1uint (tk, i)
typedef patience_sort_index_t (tk : tkind, ifirst : int, len : int) =
  [i : int]
  patience_sort_index_t (tk, ifirst, len, i)

(* A type used in temporary workspaces. *)
stadef patience_sort_link_t (ifirst : int, len : int, i : int) =
  0 <= i && i <= len
typedef patience_sort_link_t (tk : tkind, ifirst : int,
                              len : int, i : int) =
  [patience_sort_link_t (ifirst, len, i)]
  g1uint (tk, i)
typedef patience_sort_link_t (tk : tkind, ifirst : int, len : int) =
  [i : int]
  patience_sort_link_t (tk, ifirst, len, i)

(* patience_sort$lt : the order predicate for patience sort. *)
fn {a : vt@ype}
patience_sort$lt (x : &RD(a), y : &RD(a)) :<> bool

local

  typedef index_t (tk : tkind, ifirst : int, len : int) =
    patience_sort_index_t (tk, ifirst, len)
  typedef link_t (tk : tkind, ifirst : int, len : int) =
    patience_sort_link_t (tk, ifirst, len)

in

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_deal_refparams
            {ifirst, len : int}
            {n           : int | ifirst + len <= n}
            (ifirst      : g1uint (tk, ifirst),
             len         : g1uint (tk, len),
             arr         : &RD(array (a, n)),
             piles       : &array (link_t (tk, ifirst, len)?, len)
                             >> array (link_t (tk, ifirst, len), len),
             links       : &array (link_t (tk, ifirst, len)?, len)
                             >> array (link_t (tk, ifirst, len), len))
      :<!wrt> [num_piles : int | num_piles <= len]
              g1uint (tk, num_piles)

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_deal_valparams
            {ifirst, len : int}
            {n           : int | ifirst + len <= n}
            {p_piles     : addr}
            {p_links     : addr}
            (pf_piles    : !array_v (link_t (tk, ifirst, len)?,
                                     p_piles, len)
                              >> array_v (link_t (tk, ifirst, len),
                                          p_piles, len),
             pf_links    : !array_v (link_t (tk, ifirst, len)?,
                                     p_links, len)
                              >> array_v (link_t (tk, ifirst, len),
                                          p_links, len) |
             ifirst      : g1uint (tk, ifirst),
             len         : g1uint (tk, len),
             arr         : &RD(array (a, n)),
             p_piles     : ptr p_piles,
             p_links     : ptr p_links)
      :<!wrt> [num_piles   : int | num_piles <= len]
              g1uint (tk, num_piles)

  overload patience_sort_deal with patience_sort_deal_refparams
  overload patience_sort_deal with patience_sort_deal_valparams

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_merge_refparams
            {ifirst, len : int}
            {n           : int | ifirst + len <= n}
            {num_piles   : pos | num_piles <= len}
            {power       : int | num_piles <= power}
            {n_workspace : int | 4 * power <= n_workspace} (* FIXME: Reduce this size. Also don’t play "infinity" opponents. *)
            (pf_exp2     : [exponent : nat] EXP2 (exponent, power) |
             arr         : &RD(array (a, n)),
             ifirst      : g1uint (tk, ifirst),
             len         : g1uint (tk, len),
             num_piles   : g1uint (tk, num_piles),
             power       : g1uint (tk, power),
             piles       : &array (link_t (tk, ifirst, len), len) >> _,
             links       : &RD(array (link_t (tk, ifirst, len), len)),
             workspace   : &array (link_t (tk, ifirst, len)?,
                                   n_workspace) >> _,
             sorted      : &array (index_t (tk, ifirst, len)?, len)
                              >> array (index_t (tk, ifirst, len), len))
      :<!wrt> void

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_merge_valparams
            {ifirst, len  : int}
            {n            : int | ifirst + len <= n}
            {num_piles    : pos | num_piles <= len}
            {power        : int | num_piles <= power}
            {n_workspace  : int | 4 * power <= n_workspace} (* FIXME : Reduce this size. Also don’t play "infinity" opponents. *)
            {p_piles      : addr}
            {p_links      : addr}
            {p_workspace  : addr}
            (pf_exp2      : [exponent : nat] EXP2 (exponent, power),
             pf_piles     : !array_v (link_t (tk, ifirst, len),
                                      p_piles, len) >> _,
             pf_links     : !array_v (link_t (tk, ifirst, len),
                                      p_links, len) >> _,
             pf_workspace : !array_v (link_t (tk, ifirst, len)?,
                                      p_workspace, n_workspace) >> _ |
             arr          : &RD(array (a, n)),
             ifirst       : g1uint (tk, ifirst),
             len          : g1uint (tk, len),
             num_piles    : g1uint (tk, num_piles),
             power        : g1uint (tk, power),
             p_piles      : ptr p_piles,
             p_links      : ptr p_links,
             p_workspace  : ptr p_workspace,
             sorted       : &array (index_t (tk, ifirst, len)?, len)
                              >> array (index_t (tk, ifirst, len),
                                        len))
      :<!wrt> void

  overload patience_sort_merge with patience_sort_merge_refparams
  overload patience_sort_merge with patience_sort_merge_valparams

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_given_workspace (* FIXME: GET RID OF THIS ***********************************************************)
            {ifirst, len : int | 0 <= ifirst}
            {n           : int | ifirst + len <= n}
            {power       : int | len <= power}
            {n_workspace : int | (2 * len) + (4 * power)
                                    <= n_workspace}
            (pf_exp2     : [exponent : nat] EXP2 (exponent, power) |
             arr         : &RD(array (a, n)),
             ifirst      : g1uint (tk, ifirst),
             len         : g1uint (tk, len),
             power       : g1uint (tk, power),
             workspace   : &array (link_t (tk, ifirst, len)?,
                                   n_workspace) >> _,
             sorted      : &array (index_t (tk, ifirst, len)?, len)
                            >> array (index_t (tk, ifirst, len), len))
      :<!wrt> void

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_with_its_own_workspace
            {ifirst, len : int | 0 <= ifirst}
            {n        : int | ifirst + len <= n}
            (arr      : &RD(array (a, n)),
             ifirst   : g1uint (tk, ifirst),
             len      : g1uint (tk, len),
             sorted   : &array (index_t (tk, ifirst, len)?, len)
                          >> array (index_t (tk, ifirst, len), len))
      :<!wrt> void

end

overload patience_sort with patience_sort_given_workspace
overload patience_sort with patience_sort_with_its_own_workspace
