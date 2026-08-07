import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk908

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484349169101962, 362484474010487991⟩, ⟨50948473860924283, 58602043759300879⟩, true⟩

def state01 : KState := ⟨⟨362472677091026777, 362472801961027093⟩, ⟨1110796305778479660, 1118452473998572316⟩, true⟩

def words00 : List Nat := [371285119402737803, 371285119385579460, 371285119220394688, 371285119178086452, 371285119134198853, 371285119088391779, 371285118880189699, 371285118673065177, 371285118464626494, 371285118363119358]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472040621577683, 362472165520147954⟩, ⟨1168599732699875022, 1176258495498335476⟩, true⟩

def words01 : List Nat := [371285118229680085, 371285118147967873, 371285118065214759, 371285117983255094, 371285117776379322, 371285117591467068, 371285117404839249, 371285117335527535, 371285117195171544, 371285117056103673]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477949590744095, 362478074517657056⟩, ⟨631964131542521931, 639625468569683773⟩, true⟩

def words02 : List Nat := [371285116915648706, 371285116897673736, 371285116856943592, 371285116899538421, 371285116910926260, 371285116914097286, 371285116763632109, 371285116650363804, 371285116535445535, 371285116524357152]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477850198766752, 362477975154636078⟩, ⟨641019848830475944, 648683816114102514⟩, true⟩

def words03 : List Nat := [371285116449216734, 371285116365941987, 371285116315562323, 371285116319057535, 371285116295047845, 371285116293552866, 371285116291037709, 371285116289486685, 371285116178386864, 371285116103734649]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478799277513007, 362478924261650898⟩, ⟨554819158542034400, 562485693885336460⟩, true⟩

def words04 : List Nat := [371285116069758689, 371285116072931137, 371285115973648488, 371285115874451079, 371285115774052924, 371285115712110377, 371285115617522434, 371285115633189796, 371285115635576662, 371285115628672201]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486206450906255, 362486331463710835⟩, ⟨(-118163938938531542), (-110494799083705940)⟩, true⟩

def words05 : List Nat := [371285115596895463, 371285115634877686, 371285115721737209, 371285115724909232, 371285115650631774, 371285115560343123, 371285115468747549, 371285115431941127, 371285115360606133, 371285115377611368]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475168658718949, 362475293700118060⟩, ⟨884755175694745032, 892426913795662888⟩, true⟩

def words06 : List Nat := [371285115393599664, 371285115396772263, 371285115262232844, 371285115250457278, 371285115237039157, 371285115235682754, 371285115072178251, 371285114885991539, 371285114698546049, 371285114619165003]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467398628798009, 362467523698770168⟩, ⟨1590893427099401016, 1598567761778899826⟩, true⟩

def words07 : List Nat := [371285114513255888, 371285114469983693, 371285114425636166, 371285114373092630, 371285114218776234, 371285114101673660, 371285113982966650, 371285113953980040, 371285113762849236, 371285113572909461]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477021749757817, 362477146848178810⟩, ⟨716301163468288735, 723978083720157861⟩, true⟩

def words08 : List Nat := [371285113381550282, 371285113241990869, 371285113065296156, 371285112970653287, 371285112875053487, 371285112768493557, 371285112529781007, 371285112413780635, 371285112296041749, 371285112279840381]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470822715205130, 362470947842530280⟩, ⟨1279777647573803806, 1287457195067028198⟩, true⟩

def words09 : List Nat := [371285112194597427, 371285112110570599, 371285112025294223, 371285112003231304, 371285111919507806, 371285111840323914, 371285111759999535, 371285111670000153, 371285111439897634, 371285111288020567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk908
