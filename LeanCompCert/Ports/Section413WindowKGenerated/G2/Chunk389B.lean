import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389A

def state06 : KState := ⟨⟨360589205291970471, 360589214621586014⟩, ⟨(-267007733632984641), (-266762051292711949)⟩, true⟩

def words05 : List Nat := [360582373911038738, 360582373145612579, 360582372380066256, 360582372272150419, 360582371508605320, 360582370125763183, 360582368742891313, 360582367851187817, 360582367545802386, 360582367722089269]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571218020350169, 360571227354994375⟩, ⟨433855853748330376, 434101732029413518⟩, true⟩

def words06 : List Nat := [360582367722565695, 360582367538733900, 360582368111618669, 360582368684629639, 360582369091184823, 360582369091711584, 360582368842959239, 360582368215079973, 360582367587140456, 360582366737391846]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360546600863403528, 360546610203007175⟩, ⟨1393457375667394109, 1393703447243396913⟩, true⟩

def words07 : List Nat := [360582366823065702, 360582367194659046, 360582367195131519, 360582367064416214, 360582366744879467, 360582366254341480, 360582365929348971, 360582365929875914, 360582365441109392, 360582364524383353]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573768190784234, 360573777535370722⟩, ⟨334250101492636452, 334496367323911510⟩, true⟩

def words08 : List Nat := [360582363607586310, 360582362909502124, 360582362591665799, 360582362256736401, 360582361921780274, 360582360994894810, 360582359617872649, 360582358435128115, 360582357252282915, 360582356565053306]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586979250674025, 360586988600278907⟩, ⟨(-180956936863205031), (-180710475340606289)⟩, true⟩

def words09 : List Nat := [360582356345497219, 360582355713273950, 360582355104433439, 360582355578526114, 360582355621136761, 360582355663828275, 360582355664310486, 360582355199749721, 360582354997742568, 360582355117154357]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389B
