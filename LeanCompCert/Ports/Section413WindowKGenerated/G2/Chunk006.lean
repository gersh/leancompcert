import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk006

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359874108703691124, 359874108705081280⟩, ⟨245958426886451929, 245958427457479501⟩, true⟩

def state01 : KState := ⟨⟨361470699133675917, 361470699135115734⟩, ⟨(-716086983291100009), (-716086982690019147)⟩, true⟩

def words00 : List Nat := [360285274063338409, 360287800090631737, 360288693125257079, 360289583207702395, 360289583207706834, 360289394643217801, 360292625861252815, 360295846467735366, 360296786048733152, 360298707346752364]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨364161027587818756, 364161027589309500⟩, ⟨(-2380326997123151208), (-2380326996490742622)⟩, true⟩

def words01 : List Nat := [360300877087701727, 360303039749563101, 360307706490292835, 360309943702591361, 360309943702596318, 360309750568419440, 360311858593395139, 360315588176551879, 360321790498189771, 360327972844557902]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨359838349494048353, 359838349495591452⟩, ⟨308785495974749693, 308785496639879705⟩, true⟩

def words02 : List Nat := [360332502601027908, 360334660793668483, 360336450296090183, 360338234072105652, 360339373171519035, 360339373171524519, 360338165341709650, 360334903103892706, 360331651238850015, 360328485204543643]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨357258189212819438, 357258189214415242⟩, ⟨1954241294335753684, 1954241295034361650⟩, true⟩

def words03 : List Nat := [360329324389179780, 360330935228382024, 360331231264066456, 360331231264072047, 360329226025981736, 360326420832378568, 360323624446289165, 360319857063512398, 360316469801317669, 360311691237906433]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362019025106194917, 362019025107844449⟩, ⟨(-1111944597260829065), (-1111944596527561471)⟩, true⟩

def words04 : List Nat := [360306927584208224, 360304490712389330, 360304512114969744, 360305673531580772, 360305673531585999, 360304733883967944, 360305472521763346, 360306982678908033, 360308341113180705, 360310968891980300]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨363503613647877417, 363503613649582429⟩, ⟨(-2090301285228393071), (-2090301284458784569)⟩, true⟩

def words05 : List Nat := [360311796331163608, 360312621236077409, 360315695690016290, 360319947830504081, 360323416099150859, 360326873809903169, 360329083204351511, 360331684538100928, 360336490491304891, 360341281903048716]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362133849457658816, 362133849459419858⟩, ⟨(-1180529484605558908), (-1180529483798680468)⟩, true⟩

def words06 : List Nat := [360348264897283430, 360353160467981254, 360356348641281020, 360359527226090303, 360360975695965945, 360363854716970075, 360366951155041327, 360370038336198680, 360371865155236513, 360374491063296639]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362815961437457970, 362815961439276418⟩, ⟨(-1643687293589414326), (-1643687292743776938)⟩, true⟩

def words07 : List Nat := [360377027845613736, 360379557089203582, 360384205629930892, 360386844461265695, 360387613328095909, 360388379923532702, 360391252475068630, 360395214321822093, 360398774244058676, 360402323711311988]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨363762070263002142, 363762070264879267⟩, ⟨(-2297605203993390094), (-2297605203107558820)⟩, true⟩

def words08 : List Nat := [360404673083696100, 360407171417185156, 360411729976427992, 360416275226010598, 360420099182312131, 360423956211945142, 360426650568182036, 360429337103356524, 360432207651672892, 360437026555606389]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360037005650955589, 360037005652891774⟩, ⟨299719003253000405, 299719004179886277⟩, true⟩

def words09 : List Nat := [360443842497296305, 360450638768160010, 360455478971117462, 360458423050903290, 360460703606640762, 360462977618460966, 360465322487388765, 360465788205354343, 360465788205359967, 360465175658863041]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk006
