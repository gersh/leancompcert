import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk975

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488139595021592, 362488284333959282⟩, ⟨(-296567148456629276), (-287039374459536658)⟩, true⟩

def state01 : KState := ⟨⟨362485749297739415, 362485894067198180⟩, ⟨(-63500225306817897), (-53969475346552789)⟩, true⟩

def words00 : List Nat := [371285340508351586, 371285340511774178, 371285340509615548, 371285340488133586, 371285340471759539, 371285340475567024, 371285340481656886, 371285340535160740, 371285340587278017, 371285340596560544]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494958843612619, 362495103644014321⟩, ⟨(-961563232291860540), (-952029464931239352)⟩, true⟩

def words01 : List Nat := [371285340709799721, 371285340824854568, 371285341004989853, 371285341046028293, 371285341059254823, 371285341073473354, 371285341129996846, 371285341135462203, 371285341237890808, 371285341341895483]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490848006744710, 362490992838041979⟩, ⟨(-560681683123514975), (-551144902674385913)⟩, true⟩

def words02 : List Nat := [371285341444306294, 371285341447729270, 371285341474649034, 371285341543728588, 371285341635626966, 371285341674067969, 371285341695190312, 371285341717491858, 371285341804682095, 371285341866528570]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480036465506216, 362480181327616856⟩, ⟨493842433930898804, 503382219766346498⟩, true⟩

def words03 : List Nat := [371285341970465637, 371285342075725160, 371285342180064226, 371285342183487565, 371285342147524466, 371285342145087776, 371285342188141456, 371285342191624695, 371285342154031993, 371285342104936585]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494874522413417, 362495019415142340⟩, ⟨(-953524536020312598), (-943981763519015838)⟩, true⟩

def words04 : List Nat := [371285342094032010, 371285342097840600, 371285342150056750, 371285342216520666, 371285342254391670, 371285342257832411, 371285342276663831, 371285342341578355, 371285342509865840, 371285342612613212]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490915269199520, 362491060193227355⟩, ⟨(-567231169785575078), (-557685343923350468)⟩, true⟩

def words05 : List Nat := [371285342714030195, 371285342816705306, 371285343022989120, 371285343182135724, 371285343368966397, 371285343557077918, 371285343746135508, 371285343796001190, 371285343856974130, 371285343919881209]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488086589433239, 362488231543969158⟩, ⟨(-291246889308294589), (-281698086917821437)⟩, true⟩

def words06 : List Nat := [371285344085914756, 371285344113006331, 371285344126769274, 371285344141651132, 371285344169975617, 371285344173821558, 371285344246705429, 371285344328964374, 371285344402068704, 371285344435228674]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502951739512510, 362503096724996123⟩, ⟨(-1741733149095702114), (-1732181326984429420)⟩, true⟩

def words07 : List Nat := [371285344572237858, 371285344710985643, 371285344881382414, 371285344912829307, 371285344926307620, 371285344940880183, 371285345059114119, 371285345139781245, 371285345324021795, 371285345509831446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491175567311410, 362491320583662549⟩, ⟨(-592583049123775783), (-583028214801612945)⟩, true⟩

def words08 : List Nat := [371285345674991239, 371285345712116978, 371285345853220153, 371285345996153794, 371285346159046531, 371285346195987892, 371285346211209831, 371285346227491719, 371285346317895259, 371285346383021080]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484295032890614, 362484440080123163⟩, ⟨78966237219810904, 88524085416136252⟩, true⟩

def words09 : List Nat := [371285346515695153, 371285346649806777, 371285346782471220, 371285346828693823, 371285346895730415, 371285346964462101, 371285347097665952, 371285347101091909, 371285347094582666, 371285347089195050]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk975
