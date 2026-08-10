import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk899A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk899B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk899A

def state06 : KState := ⟨⟨360576684360810433, 360576737554266261⟩, ⟨469801655525710014, 473033071145038138⟩, true⟩

def words05 : List Nat := [360581997366678319, 360581997228774367, 360581997090493681, 360581997010670660, 360581996857624835, 360581996598309693, 360581996338769505, 360581996052208408, 360581995871385039, 360581995814283436]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564005898805225, 360564059104619080⟩, ⟨1610363689936319000, 1613596217343687558⟩, true⟩

def words06 : List Nat := [360581995756989408, 360581995628762512, 360581995427425323, 360581995349928870, 360581995272047779, 360581995135746229, 360581994875904470, 360581994554237772, 360581994232336487, 360581993929753500]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360544812715624034, 360544865933675580⟩, ⟨3337245296347634021, 3340478924841371133⟩, true⟩

def words07 : List Nat := [360581993731480997, 360581993530528874, 360581993329455875, 360581993049785806, 360581992646523137, 360581992179482991, 360581991712069658, 360581991368308326, 360581991027342883, 360581990616103246]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566087845174324, 360566141075471738⟩, ⟨1422775111591629519, 1426009842030726413⟩, true⟩

def words08 : List Nat := [360581990204572145, 360581989791084092, 360581989439350197, 360581989211237449, 360581988983046279, 360581988637104659, 360581988255396005, 360581987925955459, 360581987596140710, 360581987389973691]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360546609792078762, 360546663034772729⟩, ⟨3175740702632015018, 3178976548694957342⟩, true⟩

def words09 : List Nat := [360581987215062735, 360581986939291637, 360581986663255908, 360581986463186014, 360581986331650730, 360581986141945170, 360581985952102164, 360581985690187722, 360581985387398200, 360581984996424896]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk899B
