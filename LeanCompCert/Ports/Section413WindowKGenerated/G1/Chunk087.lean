import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk087

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477082184992111, 362477083125293802⟩, ⟨40473513272409603, 40479052652278603⟩, true⟩

def state01 : KState := ⟨⟨362419543230182634, 362419544172727772⟩, ⟨541103988427130058, 541109547336702022⟩, true⟩

def words00 : List Nat := [371281736331093728, 371281736331345690, 371281723978995489, 371281711392950560, 371281698809697791, 371281690302812011, 371281675184626555, 371281673179484636, 371281671174716728, 371281669264270448]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362588421004518279, 362588421949340505⟩, ⟨(-930656755923426303), (-930651177168964711)⟩, true⟩

def words01 : List Nat := [371281665790149426, 371281669447122392, 371281686190841526, 371281686191093362, 371281685458170412, 371281682080520224, 371281684482823169, 371281684483100449, 371281695896627269, 371281708134735648]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362374986615809881, 362374987562909991⟩, ⟨931503923197916606, 931509521827251652⟩, true⟩

def words02 : List Nat := [371281718483703528, 371281718630407487, 371281721586101209, 371281724541241924, 371281731055684964, 371281731055937134, 371281720143404550, 371281709338474301, 371281698535919202, 371281689684539688]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362407852129449388, 362407853078821690⟩, ⟨644873166483001515, 644878784959988189⟩, true⟩

def words03 : List Nat := [371281678280953825, 371281679098345677, 371281679098534715, 371281678332412233, 371281666082847611, 371281657895023696, 371281654546721079, 371281654546974225, 371281646279702727, 371281637836826266]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484638277882911, 362484639229519549⟩, ⟨(-26334868255187400), (-26329229976301698)⟩, true⟩

def words04 : List Nat := [371281633971608745, 371281633971887073, 371281638783149979, 371281643881387032, 371281645478739193, 371281645478992089, 371281629726999083, 371281626971306805, 371281630174398842, 371281630518517801]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490090660638718, 362490091614579908⟩, ⟨(-73832460341357773), (-73826801885827051)⟩, true⟩

def words05 : List Nat := [371281630963018074, 371281631407504570, 371281644824530505, 371281651688891737, 371281659048407850, 371281666406338241, 371281671468153634, 371281671468407015, 371281663897155131, 371281664859428005]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362437596932872684, 362437597889070906⟩, ⟨386728815094245324, 386734493333249688⟩, true⟩

def words06 : List Nat := [371281678776272508, 371281680387680941, 371281680647480267, 371281680907307215, 371281685200487123, 371281685200768492, 371281687608649329, 371281692072841868, 371281695322484146, 371281695322746306]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362619528577311362, 362619529535803360⟩, ⟨(-1210045817189232309), (-1210040118822329997)⟩, true⟩

def words07 : List Nat := [371281690295281480, 371281690256760878, 371281700935238903, 371281700935492731, 371281697323168691, 371281692509337976, 371281693260744632, 371281696055587130, 371281711754334013, 371281727449614734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362446221271240553, 362446222232024919⟩, ⟨312435064373549868, 312440782879179518⟩, true⟩

def words08 : List Nat := [371281743229227804, 371281743229481959, 371281753262598134, 371281764722769946, 371281776541035776, 371281776541290383, 371281774873256441, 371281771558372930, 371281768244144003, 371281767258518569]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362346308591133669, 362346309554214340⟩, ⟨1191658812726867869, 1191664551428724983⟩, true⟩

def words09 : List Nat := [371281768778164905, 371281774339998043, 371281779711537220, 371281779711791779, 371281767919111049, 371281760134616222, 371281754012594893, 371281754012849668, 371281741370201110, 371281725980513059]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk087
