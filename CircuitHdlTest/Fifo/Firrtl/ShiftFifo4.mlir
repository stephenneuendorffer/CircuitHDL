"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input rst : i1, input s_valid : i1, input s_data : i8, input m_ready : i1, output m_valid : i1, output m_data : i8, output s_ready : i1>, parameters = [], sym_name = "ShiftFifo4"}> ({
  ^bb0(%arg0: i1, %arg1: i1, %arg2: i1, %arg3: i8, %arg4: i1):
    %0 = "hw.constant"() <{value = 0 : i2}> : () -> i2
    %1 = "hw.constant"() <{value = true}> : () -> i1
    %2 = "hw.constant"() <{value = -4 : i3}> : () -> i3
    %3 = "hw.constant"() <{value = 1 : i3}> : () -> i3
    %4 = "hw.constant"() <{value = 2 : i3}> : () -> i3
    %5 = "hw.constant"() <{value = 3 : i3}> : () -> i3
    %6 = "hw.constant"() <{value = 0 : i3}> : () -> i3
    %7 = "hw.constant"() <{value = 0 : i8}> : () -> i8
    %8 = "seq.to_clock"(%arg0) {sv.namehint = "clock"} : (i1) -> !seq.clock
    %9 = "seq.firreg"(%26, %8, %arg1, %6) <{name = "count"}> : (i3, !seq.clock, i1, i3) -> i3
    %10 = "seq.firreg"(%30, %8, %arg1, %7) <{name = "r0"}> : (i8, !seq.clock, i1, i8) -> i8
    %11 = "seq.firreg"(%34, %8, %arg1, %7) <{name = "r1"}> : (i8, !seq.clock, i1, i8) -> i8
    %12 = "seq.firreg"(%38, %8, %arg1, %7) <{name = "r2"}> : (i8, !seq.clock, i1, i8) -> i8
    %13 = "seq.firreg"(%41, %8, %arg1, %7) <{name = "r3"}> : (i8, !seq.clock, i1, i8) -> i8
    %14 = "comb.xor"(%arg1, %1) {sv.namehint = "notRst"} : (i1, i1) -> i1
    %15 = "comb.icmp"(%9, %2) <{predicate = 1 : i64}> : (i3, i3) -> i1
    %16 = "comb.and"(%14, %15) {sv.namehint = "sRdy"} : (i1, i1) -> i1
    %17 = "comb.icmp"(%9, %6) <{predicate = 1 : i64}> : (i3, i3) -> i1
    %18 = "comb.and"(%14, %17) {sv.namehint = "mVld"} : (i1, i1) -> i1
    %19 = "comb.and"(%arg2, %16) {sv.namehint = "wfire"} : (i1, i1) -> i1
    %20 = "comb.and"(%18, %arg4) {sv.namehint = "rfire"} : (i1, i1) -> i1
    %21 = "comb.concat"(%0, %20) : (i2, i1) -> i3
    %22 = "comb.sub"(%9, %21) {sv.namehint = "widx"} : (i3, i3) -> i3
    %23 = "comb.concat"(%0, %19) : (i2, i1) -> i3
    %24 = "comb.add"(%23, %9) {sv.namehint = "cmid"} : (i3, i3) -> i3
    %25 = "comb.concat"(%0, %20) : (i2, i1) -> i3
    %26 = "comb.sub"(%24, %25) {sv.namehint = "cnext"} : (i3, i3) -> i3
    %27 = "comb.icmp"(%22, %6) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %28 = "comb.and"(%19, %27) : (i1, i1) -> i1
    %29 = "comb.mux"(%20, %11, %10) : (i1, i8, i8) -> i8
    %30 = "comb.mux"(%28, %arg3, %29) : (i1, i8, i8) -> i8
    %31 = "comb.icmp"(%22, %3) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %32 = "comb.and"(%19, %31) : (i1, i1) -> i1
    %33 = "comb.mux"(%20, %12, %11) : (i1, i8, i8) -> i8
    %34 = "comb.mux"(%32, %arg3, %33) : (i1, i8, i8) -> i8
    %35 = "comb.icmp"(%22, %4) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %36 = "comb.and"(%19, %35) : (i1, i1) -> i1
    %37 = "comb.mux"(%20, %13, %12) : (i1, i8, i8) -> i8
    %38 = "comb.mux"(%36, %arg3, %37) : (i1, i8, i8) -> i8
    %39 = "comb.icmp"(%22, %5) <{predicate = 0 : i64}> : (i3, i3) -> i1
    %40 = "comb.and"(%19, %39) : (i1, i1) -> i1
    %41 = "comb.mux"(%40, %arg3, %13) : (i1, i8, i8) -> i8
    "hw.output"(%18, %10, %16) : (i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

