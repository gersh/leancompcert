import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk817A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk817B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk817A

def state06 : KState := ⟨⟨362477744932448133, 362477845338065182⟩, ⟨597467750882506565, 603010922940228881⟩, true⟩

def words05 : List Nat := [371285220283113399, 371285220509002702, 371285220683231625, 371285220686063680, 371285220730439982, 371285220777178909, 371285220888390129, 371285220891221111, 371285220803211496, 371285220716281183]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484756969243884, 362484857400169448⟩, ⟨24145315369489396, 29690556783027564⟩, true⟩

def words06 : List Nat := [371285220687394860, 371285220690514744, 371285220738168306, 371285220802232530, 371285220833268718, 371285220836099874, 371285220667513872, 371285220561992505, 371285220495622203, 371285220498576970]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492906051130649, 362493006507827542⟩, ⟨(-642231406847625622), (-636684057984732528)⟩, true⟩

def words07 : List Nat := [371285220496253288, 371285220481876376, 371285220598514804, 371285220693980781, 371285220832069636, 371285220971281578, 371285221109392673, 371285221112226510, 371285221177152104, 371285221275830077]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477745836676200, 362477846318612764⟩, ⟨597648266961870741, 603197680056228417⟩, true⟩

def words08 : List Nat := [371285221436099385, 371285221438931483, 371285221416681227, 371285221390788174, 371285221363798987, 371285221343719016, 371285221258487357, 371285221264685091, 371285221272032976, 371285221274965084]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497342547911220, 362497443055483355⟩, ⟨(-1005270688805218996), (-999719178853090508)⟩, true⟩

def words09 : List Nat := [371285221227263061, 371285221271272349, 371285221450131795, 371285221452964198, 371285221432911418, 371285221375767214, 371285221392024542, 371285221395146278, 371285221546417010, 371285221699034741]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk817B
