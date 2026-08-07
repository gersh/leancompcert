import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk631

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562743832625222, 360562769283047196⟩, ⟨1256722958118860597, 1257807804536929939⟩, true⟩

def state01 : KState := ⟨⟨360592928384198514, 360592953842984286⟩, ⟨(-648027169084898598), (-646941794869010306)⟩, true⟩

def words00 : List Nat := [360582702530535470, 360582702441426029, 360582702729264692, 360582703017267213, 360582703063618168, 360582703064504695, 360582702925199012, 360582702824685280, 360582702823292003, 360582702986638023]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594752053061308, 360594777520299527⟩, ⟨(-763102255686604096), (-762016347995223294)⟩, true⟩

def words01 : List Nat := [360582703018109509, 360582703049693743, 360582703331828962, 360582703775559847, 360582704080869285, 360582704386310900, 360582704566897975, 360582704824948466, 360582705016943676, 360582705209214544]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594396643684595, 360594422119275448⟩, ⟨(-740747782035257263), (-739661347084836583)⟩, true⟩

def words02 : List Nat := [360582705393604250, 360582705438162563, 360582705438952718, 360582705339192250, 360582705239290862, 360582705054714471, 360582705312661076, 360582705570773617, 360582705638916630, 360582705825424807]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603987943744471, 360604013427716973⟩, ⟨(-1346352890835822239), (-1345265926711142629)⟩, true⟩

def words03 : List Nat := [360582706262369081, 360582706699559695, 360582707052222096, 360582707155065587, 360582707155892339, 360582707021131637, 360582706886206871, 360582707008049420, 360582707346213816, 360582707684591094]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589120117322485, 360589145609731834⟩, ⟨(-407662734593468991), (-406575237724073043)⟩, true⟩

def words04 : List Nat := [360582707867043945, 360582707867931084, 360582708058708143, 360582708255708212, 360582708353264780, 360582708354151948, 360582708201886736, 360582707838990523, 360582707475935890, 360582707465637140]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360576121758889307, 360576147259653690⟩, ⟨413287056192452141, 414375080724380335⟩, true⟩

def words05 : List Nat := [360582707606755180, 360582707748033876, 360582707761219696, 360582707887226370, 360582707887970947, 360582707866031635, 360582708019397929, 360582708081907899, 360582708082698855, 360582707979741157]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588348299720035, 360588373808872617⟩, ⟨(-358996460133136084), (-357907905761059600)⟩, true⟩

def words06 : List Nat := [360582707876598380, 360582707859373077, 360582708148380708, 360582708437549116, 360582708514378089, 360582708515265601, 360582708342258828, 360582708167239444, 360582708018722315, 360582708109330722]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577233129340914, 360577258646952343⟩, ⟨343165989484435124, 344255078242159048⟩, true⟩

def words07 : List Nat := [360582708110128784, 360582708076305752, 360582708046114476, 360582708175760880, 360582708176519122, 360582708115142857, 360582708053671433, 360582707866280417, 360582707530494744, 360582707445278430]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578321198408505, 360578346724387036⟩, ⟨274388136868113827, 275477754301315361⟩, true⟩

def words08 : List Nat := [360582707359756456, 360582707265987119, 360582707178638519, 360582706965412745, 360582706752042951, 360582706475708729, 360582706372672867, 360582706422355576, 360582706423170061, 360582706239410004]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360608441591962688, 360608467126320784⟩, ⟨(-1629153259449892766), (-1628063112469843578)⟩, true⟩

def words09 : List Nat := [360582706236922416, 360582706303682046, 360582706443137084, 360582706473062919, 360582706473887169, 360582706255007193, 360582706066259553, 360582706224787489, 360582706633114597, 360582707041631146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk631
