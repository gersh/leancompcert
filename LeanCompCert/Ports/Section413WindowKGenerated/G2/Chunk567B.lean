import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567A

def state06 : KState := ⟨⟨360613251264246208, 360613271684408531⟩, ⟨(-1787259242992166167), (-1786476162204663313)⟩, true⟩

def words05 : List Nat := [360581794420192915, 360581794754634312, 360581795080008507, 360581795560599701, 360581795962132583, 360581796363794074, 360581796609480931, 360581796918291707, 360581797473454650, 360581798028866792]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619116669737058, 360619137097347444⟩, ⟨(-2120300388395858779), (-2119516884818700939)⟩, true⟩

def words06 : List Nat := [360581798770651717, 360581799289627228, 360581799529272589, 360581799768975982, 360581799929824886, 360581800245657285, 360581800871179212, 360581801496830599, 360581801939128490, 360581802597606050]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360624059879165236, 360624080314237583⟩, ⟨(-2401053396270681733), (-2400269469041036105)⟩, true⟩

def words07 : List Nat := [360581803151386901, 360581803705382978, 360581804569012905, 360581805123670188, 360581805412699441, 360581805701779636, 360581805982468014, 360581806418044381, 360581807163204674, 360581807908520160]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360629109150061909, 360629129592673301⟩, ⟨(-2687853717251967344), (-2687069361918783858)⟩, true⟩

def words08 : List Nat := [360581808495839579, 360581809166605642, 360581810146989063, 360581811127589294, 360581811960387053, 360581812484296615, 360581812807889999, 360581813131557397, 360581813702311914, 360581814536380600]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575003840401946, 360575024290473083⟩, ⟨385028200489068375, 385812979498927533⟩, true⟩

def words09 : List Nat := [360581815235306928, 360581815934348008, 360581816399764251, 360581816642677825, 360581816734309550, 360581816826147400, 360581816854520521, 360581816890563135, 360581816891274564, 360581816772506515]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567B
