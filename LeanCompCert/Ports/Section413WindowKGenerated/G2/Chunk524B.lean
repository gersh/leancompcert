import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk524A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk524B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk524A

def state06 : KState := ⟨⟨360583513026124464, 360583530358525576⟩, ⟨(-77493872001783257), (-76879507271047111)⟩, true⟩

def words05 : List Nat := [360582066341911516, 360582066139368388, 360582066096030979, 360582066096757513, 360582065894398993, 360582065379820483, 360582064865122330, 360582064841114949, 360582064869643562, 360582064898330936]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571731607419397, 360571748946746480⟩, ⟨540448237350317123, 541062965450460705⟩, true⟩

def words06 : List Nat := [360582064898985593, 360582064678292867, 360582064339468792, 360582064169464280, 360582063999284352, 360582063579723045, 360582062956812075, 360582062152287145, 360582061347650378, 360582060800481004]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541361858119407, 360541379204293627⟩, ⟨2134186957478446407, 2134802044883105913⟩, true⟩

def words07 : List Nat := [360582060689519504, 360582060775231324, 360582060775878852, 360582060679957952, 360582060221761469, 360582059669379521, 360582059116805568, 360582058820908021, 360582058371301057, 360582057596917162]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589056902509264, 360589074255543463⟩, ⟨(-369217778254436643), (-368602330803742263)⟩, true⟩

def words08 : List Nat := [360582056822404625, 360582055924961188, 360582055210145713, 360582054714734145, 360582054219284830, 360582053413320051, 360582052749075102, 360582052352447555, 360582051955613736, 360582052054960435]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568323587522096, 360568340947491854⟩, ⟨719178470071085627, 719794281602859639⟩, true⟩

def words09 : List Nat := [360582052055608163, 360582052008642621, 360582051961544969, 360582052073354710, 360582052151699703, 360582052230162345, 360582052230817548, 360582052083948613, 360582051575070782, 360582051314760480]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk524B
