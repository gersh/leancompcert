import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk144

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362434778271835128, 362434780968454291⟩, ⟨706543869697185324, 706570139550930592⟩, true⟩

def state01 : KState := ⟨⟨362464798376278773, 362464801076762435⟩, ⟨274178094758123337, 274204420280970889⟩, true⟩

def words00 : List Nat := [371283846325042464, 371283846325477273, 371283842807174402, 371283839282432513, 371283835758016559, 371283833097166476, 371283829059692380, 371283829439829778, 371283829835524778, 371283829835976937]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362529888191164874, 362529890895573609⟩, ⟨(-664152136354409540), (-664125754251356336)⟩, true⟩

def words01 : List Nat := [371283831989845053, 371283835463882918, 371283839824064710, 371283839824499040, 371283837789010092, 371283835256712271, 371283833417853100, 371283833418336147, 371283835017533352, 371283838211692370]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362442958876356984, 362442961584682212⟩, ⟨589568489619881928, 589594928219102360⟩, true⟩

def words02 : List Nat := [371283840261312537, 371283840261747119, 371283836371378861, 371283836819931944, 371283838582773602, 371283838583208226, 371283833961167243, 371283828185841740, 371283822411144837, 371283820554066766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362445732292247917, 362445735004494149⟩, ⟨549876468729331487, 549902963928597817⟩, true⟩

def words03 : List Nat := [371283819672853407, 371283821622888372, 371283823042709398, 371283823043151852, 371283820514386473, 371283819481636724, 371283822193582680, 371283822194017821, 371283819564145664, 371283816927203886]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478342713676812, 362478345429827432⟩, ⟨78715539724589871, 78742091322811285⟩, true⟩

def words04 : List Nat := [371283814290435099, 371283813608228913, 371283811139957711, 371283809658003244, 371283808176125675, 371283805921409567, 371283798346460787, 371283795543760052, 371283794709051460, 371283794709503752]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362462144152727915, 362462146872838413⟩, ⟨313030437256352960, 313057046095140810⟩, true⟩

def words05 : List Nat := [371283794332743017, 371283793950544912, 371283796852046699, 371283798627021428, 371283800239883521, 371283801852689132, 371283803221954120, 371283803222389763, 371283798234507872, 371283796737713596]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362405130163098466, 362405132887096226⟩, ⟨1138103356809591646, 1138130021878565340⟩, true⟩

def words06 : List Nat := [371283798505293188, 371283798505736414, 371283797832122472, 371283797180850829, 371283796529499084, 371283795963170580, 371283793014069481, 371283791374969539, 371283789735960825, 371283787346106494]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507867499744571, 362507870227691461⟩, ⟨(-349121986894429763), (-349095264662082147)⟩, true⟩

def words07 : List Nat := [371283781911087179, 371283780009471507, 371283779695796179, 371283779696232445, 371283774941749545, 371283769582850451, 371283764224508046, 371283762857407482, 371283761438199974, 371283763103552101]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362443241291962893, 362443244023856865⟩, ⟨586758219921558922, 586784999327688448⟩, true⟩

def words08 : List Nat := [371283764795351886, 371283764795790491, 371283761951774186, 371283761058111773, 371283760756720659, 371283760757157439, 371283755018488157, 371283748391583448, 371283741765412940, 371283739883023718]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362370305454282528, 362370308190104675⟩, ⟨1644240441247918862, 1644267277593550504⟩, true⟩

def words09 : List Nat := [371283738058652460, 371283739028872613, 371283739991341646, 371283739991778574, 371283734629823983, 371283729861804281, 371283725094216914, 371283721539280227, 371283713753973086, 371283705933386989]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk144
