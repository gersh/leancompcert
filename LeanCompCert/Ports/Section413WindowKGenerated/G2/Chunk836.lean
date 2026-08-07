import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk836

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617587496036863, 360617633174122143⟩, ⟨(-2944504703626984696), (-2941925785591009350)⟩, true⟩

def state01 : KState := ⟨⟨360600480855832320, 360600526545360445⟩, ⟨(-1514457096138496598), (-1511877221424198004)⟩, true⟩

def words00 : List Nat := [360582443407502344, 360582443577104493, 360582443746249324, 360582443915737526, 360582444008449897, 360582444052868195, 360582444053938640, 360582444005866985, 360582444051198205, 360582444268848692]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570652842400058, 360570698543216746⟩, ⟨979638076126199354, 982218894733888842⟩, true⟩

def words01 : List Nat := [360582444505093203, 360582444741555299, 360582444892906400, 360582444943924659, 360582444944946061, 360582444898653936, 360582444947309038, 360582444948508655, 360582444902188179, 360582444762957644]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582597368938429, 360582643081098591⟩, ⟨(-19138200935053538), (-16556433730933326)⟩, true⟩

def words02 : List Nat := [360582444625904281, 360582444760148567, 360582444941920254, 360582445123914889, 360582445177125076, 360582445178324778, 360582445113986794, 360582445140594499, 360582445141585984, 360582445111042859]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585393551992101, 360585439275572705⟩, ⟨(-253051399820276028), (-250468677469402942)⟩, true⟩

def words03 : List Nat := [360582445112111991, 360582445031524333, 360582444950715291, 360582444916373797, 360582444917378296, 360582444882361796, 360582444847203239, 360582444740490533, 360582444670212582, 360582444707388808]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599950304787806, 360599996039685018⟩, ⟨(-1470678194622868540), (-1468094525693997460)⟩, true⟩

def words04 : List Nat := [360582444887010797, 360582445025607085, 360582445051306773, 360582445077125956, 360582445078130121, 360582445128982265, 360582445308353865, 360582445487951178, 360582445595793279, 360582445806864203]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360603708797923081, 360603754544143100⟩, ⟨(-1785098879800926638), (-1782514263664799458)⟩, true⟩

def words05 : List Nat := [360582446085025123, 360582446363530468, 360582446784476902, 360582447095001208, 360582447267025147, 360582447439114993, 360582447498366179, 360582447638145958, 360582447893800646, 360582448149721987]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604460823275238, 360604506580923573⟩, ⟨(-1848109999396318315), (-1845524427110331783)⟩, true⟩

def words06 : List Nat := [360582448324165493, 360582448404330678, 360582448627029675, 360582448850111631, 360582449005817348, 360582449139792635, 360582449196789521, 360582449253921724, 360582449397444657, 360582449662431977]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596420909816564, 360596466678781084⟩, ⟨(-1175372739058307795), (-1172786219890598677)⟩, true⟩

def words07 : List Nat := [360582449923328433, 360582450184431790, 360582450373661300, 360582450586953933, 360582450762807736, 360582450938977410, 360582451137015054, 360582451377291212, 360582451545847503, 360582451714573073]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609982542626925, 360610028322917051⟩, ⟨(-2310315321196874228), (-2307727854245066186)⟩, true⟩

def words08 : List Nat := [360582451871414727, 360582452100638487, 360582452431526725, 360582452762637046, 360582452957576563, 360582453010101926, 360582453161462901, 360582453313181610, 360582453607201116, 360582453937926490]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589232231511708, 360589278023269833⟩, ⟨(-573548685965570273), (-570960259204500557)⟩, true⟩

def words09 : List Nat := [360582454165776922, 360582454393761499, 360582454735910193, 360582455194589423, 360582455584994795, 360582455975584698, 360582456274408432, 360582456430915113, 360582456513409971, 360582456596295192]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk836
