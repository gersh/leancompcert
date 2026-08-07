import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592605701202254, 360592615000949105⟩, ⟨(-398237998805843686), (-397993479251045914)⟩, true⟩

def state01 : KState := ⟨⟨360577735791445098, 360577745096195906⟩, ⟨180167066143954558, 180411780377729540⟩, true⟩

def words00 : List Nat := [360582384069584115, 360582384002730957, 360582383669316039, 360582383832529662, 360582383832970150, 360582383703753646, 360582383618722375, 360582383020540745, 360582382422291391, 360582381739227974]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559281411617970, 360559290721330209⟩, ⟨898302328183574693, 898547235490779205⟩, true⟩

def words01 : List Nat := [360582382009008385, 360582382398030799, 360582382398508762, 360582382206042695, 360582381356930229, 360582380220897348, 360582379084762511, 360582378607481543, 360582378344700044, 360582377752046828]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592371116937184, 360592380431613092⟩, ⟨(-389568534839163682), (-389323434321435170)⟩, true⟩

def words02 : List Nat := [360582377224713227, 360582377711045339, 360582378855725791, 360582380000448442, 360582380580065621, 360582380580591886, 360582380503782046, 360582380246288551, 360582379988657092, 360582380086532785]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581980456811620, 360581989776500627⟩, ⟨15056300722233536, 15301596423975258⟩, true⟩

def words03 : List Nat := [360582380087002616, 360582379948854720, 360582380330200773, 360582381375485095, 360582382045186743, 360582382714938228, 360582383054842909, 360582383055369389, 360582382739157555, 360582382729670221]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360548679182168752, 360548688506819588⟩, ⟨1311834674100775927, 1312080163040986737⟩, true⟩

def words04 : List Nat := [360582382720012346, 360582382693321466, 360582382010589348, 360582380997131209, 360582379983639289, 360582378803692387, 360582377952966364, 360582377003591650, 360582376054196599, 360582374775447085]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389
