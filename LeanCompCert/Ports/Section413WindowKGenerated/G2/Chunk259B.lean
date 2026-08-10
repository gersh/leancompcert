import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259A

def state06 : KState := ⟨⟨360528357863475697, 360528361866448694⟩, ⟨1423242034189064434, 1423312329041366550⟩, true⟩

def words05 : List Nat := [360583190639957220, 360583192286154077, 360583192987616700, 360583193062139636, 360583193062424770, 360583192429257984, 360583192191862280, 360583192192202480, 360583191109479678, 360583188997767699]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570331269866587, 360570335276052719⟩, ⟨333207315410717868, 333277693692266384⟩, true⟩

def words06 : List Nat := [360583186886140717, 360583185190156198, 360583184238530466, 360583183245353750, 360583182252229937, 360583179967194636, 360583176204297182, 360583173128242850, 360583170052326213, 360583168456402826]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360553596775345579, 360553600784773791⟩, ⟨767840265186475845, 767910727680658613⟩, true⟩

def words07 : List Nat := [360583167962573195, 360583166342966509, 360583164723420168, 360583163846422143, 360583163846707587, 360583163579438292, 360583163312156929, 360583161906938960, 360583159686871836, 360583158549503609]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594987645934462, 360594991658568217⟩, ⟨(-307674327761496096), (-307603781970987002)⟩, true⟩

def words08 : List Nat := [360583157752883460, 360583157893827210, 360583157894133488, 360583157300820388, 360583156707491593, 360583155733957974, 360583156128960990, 360583156534716405, 360583156535019984, 360583156647142301]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360623682851490662, 360623686867346358⟩, ⟨(-1054016206764284263), (-1053945577219695421)⟩, true⟩

def words09 : List Nat := [360583156701087889, 360583156755128058, 360583156755406376, 360583156274861410, 360583154985632997, 360583152450214821, 360583149914926728, 360583148939210232, 360583150498637141, 360583152058022883]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk259B
