// Lean compiler output
// Module: GameTheory.ZeroSum
// Imports: Init Mathlib.Data.Real.EReal Mathlib.Data.Real.NNReal Mathlib.Data.Fintype.Basic Mathlib.Algebra.BigOperators.Basic Mathlib.Topology.Algebra.Order.Compact Mathlib.Topology.MetricSpace.Basic Mathlib.Topology.Order.Basic Mathlib.Topology.Order.Lattice Mathlib.Topology.MetricSpace.PseudoMetric GameTheory.Simplex
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
LEAN_EXPORT lean_object* l_zerosumFGame_sumxC(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumyC___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_instCoeFunZerosumGameForAllReal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zerosumFGame_one__matrix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zerosumFGame_sumxC___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_Coe_coeDelaborator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zerosumFGame_sumyC___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zerosumFGame_sumyC___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCoeFunZerosumGameForAllReal___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumxC___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumyC___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zerosumFGame_sumxC___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumxC___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_zerosumFGame_sumxC___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_zerosumFGame_one__matrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zerosumGame_g_delaborator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zerosumFGame_sumyC(lean_object*, lean_object*);
lean_object* l_List_foldrTR___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_zerosumGame_g_delaborator___closed__1;
static lean_object* l_Multiset_sum___at_zerosumFGame_sumxC___spec__2___closed__1;
LEAN_EXPORT lean_object* l_instCoeFunZerosumGameForAllReal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instCoeFunZerosumGameForAllReal(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instCoeFunZerosumGameForAllReal___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_zerosumGame_g_delaborator___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_zerosumGame_g_delaborator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_zerosumGame_g_delaborator___closed__1;
x_9 = l_Std_Tactic_Coe_coeDelaborator(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Multiset_sum___at_zerosumFGame_sumxC___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_zerosumFGame_sumxC___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Multiset_sum___at_zerosumFGame_sumxC___spec__2___closed__1;
x_3 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_4 = l_List_foldrTR___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumxC___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_), 2, 0);
x_5 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_6 = l_List_foldrTR___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumxC___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_zerosumFGame_sumxC___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_sumxC___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_2(x_2, x_4, x_3);
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_sumxC___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_zerosumFGame_sumxC___rarg___lambda__1), 4, 3);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Finset_sum___at_zerosumFGame_sumxC___spec__1___rarg(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_sumxC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_zerosumFGame_sumxC___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumyC___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = l_Multiset_sum___at_zerosumFGame_sumxC___spec__2___closed__1;
x_5 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_6 = l_List_foldrTR___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_zerosumFGame_sumyC___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_sum___at_zerosumFGame_sumyC___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_sumyC___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_2(x_2, x_3, x_4);
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_sumyC___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_zerosumFGame_sumyC___rarg___lambda__1), 4, 3);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Finset_sum___at_zerosumFGame_sumyC___spec__1___rarg(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_sumyC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_zerosumFGame_sumyC___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_one__matrix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
return x_5;
}
}
LEAN_EXPORT lean_object* l_zerosumFGame_one__matrix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_zerosumFGame_one__matrix(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_EReal(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_NNReal(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Algebra_Order_Compact(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Order_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Order_Lattice(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_PseudoMetric(uint8_t builtin, lean_object*);
lean_object* initialize_GameTheory_Simplex(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GameTheory_ZeroSum(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_EReal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_NNReal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Algebra_Order_Compact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Order_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Order_Lattice(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_PseudoMetric(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GameTheory_Simplex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_zerosumGame_g_delaborator___closed__1 = _init_l_zerosumGame_g_delaborator___closed__1();
lean_mark_persistent(l_zerosumGame_g_delaborator___closed__1);
l_Multiset_sum___at_zerosumFGame_sumxC___spec__2___closed__1 = _init_l_Multiset_sum___at_zerosumFGame_sumxC___spec__2___closed__1();
lean_mark_persistent(l_Multiset_sum___at_zerosumFGame_sumxC___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
