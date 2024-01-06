// Lean compiler output
// Module: GameTheory.Simplex
// Imports: Init Mathlib.Data.Real.EReal Mathlib.Data.Real.NNReal Mathlib.Data.Fintype.Basic Mathlib.Algebra.BigOperators.Basic Mathlib.Topology.Algebra.Order.Compact Mathlib.Topology.MetricSpace.Basic Mathlib.Topology.MetricSpace.Bounded Mathlib.Analysis.NormedSpace.FiniteDimension Mathlib.Topology.Separation Mathlib.Data.Finset.Lattice Mathlib.Topology.Algebra.Order.Compact
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
static lean_object* l_S_metricS___rarg___closed__2;
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_linear__comb___elambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1004_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_metricS___rarg___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_S_metricS___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_MetricSpace_induced___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_coe__fun(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_linear__comb___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_linear__comb(lean_object*);
static lean_object* l_S_metricS___rarg___closed__1;
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
LEAN_EXPORT lean_object* l_S_linear__comb___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_linear__comb___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_linear__comb___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Real_metricSpace;
LEAN_EXPORT lean_object* l_S_metricS___rarg___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_S_metricS___rarg(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_coe__fun___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_metricS(lean_object*);
lean_object* l_pseudoMetricSpacePi___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_coe__fun___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_S_coe__fun___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_S_coe__fun(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_S_coe__fun___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_S_coe__fun___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_S_coe__fun(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_S_linear__comb___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
x_5 = lean_apply_1(x_2, x_4);
lean_inc(x_1);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_1, x_5);
x_7 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1004_), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_8, x_7);
x_10 = lean_apply_1(x_3, x_4);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_9, x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_S_linear__comb___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_S_linear__comb___elambda__1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_S_linear__comb___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_S_linear__comb___elambda__1___rarg), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_S_linear__comb(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_S_linear__comb___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_S_linear__comb___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_S_linear__comb___elambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_S_linear__comb___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_S_linear__comb___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_S_metricS___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_S_metricS___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Real_metricSpace;
return x_2;
}
}
static lean_object* _init_l_S_metricS___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_S_metricS___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_S_metricS___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_S_metricS___rarg___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_S_metricS___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_S_metricS___rarg___closed__1;
x_3 = l_pseudoMetricSpacePi___rarg(x_1, x_2);
x_4 = l_S_metricS___rarg___closed__2;
x_5 = l_MetricSpace_induced___rarg(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_S_metricS(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_S_metricS___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_S_metricS___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_S_metricS___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_EReal(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_NNReal(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Algebra_Order_Compact(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Bounded(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_NormedSpace_FiniteDimension(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Separation(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Lattice(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Algebra_Order_Compact(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GameTheory_Simplex(uint8_t builtin, lean_object* w) {
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
res = initialize_Mathlib_Topology_MetricSpace_Bounded(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_NormedSpace_FiniteDimension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Separation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Lattice(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Algebra_Order_Compact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_S_metricS___rarg___closed__1 = _init_l_S_metricS___rarg___closed__1();
lean_mark_persistent(l_S_metricS___rarg___closed__1);
l_S_metricS___rarg___closed__2 = _init_l_S_metricS___rarg___closed__2();
lean_mark_persistent(l_S_metricS___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
