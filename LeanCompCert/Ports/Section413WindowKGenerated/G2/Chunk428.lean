import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk428

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360660255454018614, 360660266799995162⟩, ⟨(-3315475421521616437), (-3315147244595827273)⟩, true⟩

def state01 : KState := ⟨⟨360609538772466778, 360609550123997365⟩, ⟨(-1144720951812964620), (-1144392537146642828)⟩, true⟩

def words00 : List Nat := [360582813294996170, 360582814148414284, 360582815251215066, 360582816354141307, 360582817082266352, 360582817633091119, 360582817853901667, 360582818074764509, 360582818225711375, 360582818850793127]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559906140019597, 360559917497048664⟩, ⟨980390618657767626, 980719268742136648⟩, true⟩

def words01 : List Nat := [360582819797537710, 360582820744363437, 360582821330662215, 360582821374055867, 360582821374544310, 360582821276955613, 360582821443938090, 360582821444521797, 360582821330460834, 360582820796178560]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360630810526310506, 360630821888851322⟩, ⟨(-2056137022077739798), (-2055808135954154318)⟩, true⟩

def words02 : List Nat := [360582820272479390, 360582820657066904, 360582820848059768, 360582821039151182, 360582821039690043, 360582820766291458, 360582821206446982, 360582821646753206, 360582822632212715, 360582823753483151]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605632698350885, 360605644066465148⟩, ⟨(-977686294933633651), (-977357170072791571)⟩, true⟩

def words03 : List Nat := [360582824600976550, 360582825448489269, 360582826112094194, 360582827232231199, 360582828060235535, 360582828888294118, 360582829418504552, 360582829419088485, 360582829939494487, 360582830472709802]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588745116621854, 360588756490233337⟩, ⟨(-254096814703574175), (-253767454314449777)⟩, true⟩

def words04 : List Nat := [360582831550837692, 360582832308254483, 360582832790630088, 360582833273046899, 360582833273540278, 360582833610172724, 360582833941902563, 360582834273723304, 360582834274249801, 360582834400799848]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360652506158143054, 360652517537264201⟩, ⟨(-2986606641806266991), (-2986277045299595895)⟩, true⟩

def words05 : List Nat := [360582834927614127, 360582835454574808, 360582836526126039, 360582837612380994, 360582838240542461, 360582838868724083, 360582839676058329, 360582840757790459, 360582842383946068, 360582844010157984]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360634531853086456, 360634543237778205⟩, ⟨(-2216319609248646448), (-2215989773958324194)⟩, true⟩

def words06 : List Nat := [360582845173639637, 360582846054253677, 360582847479273668, 360582848904399813, 360582850188609811, 360582850931331499, 360582851256537892, 360582851581794581, 360582852316329231, 360582853522727044]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360627877183955324, 360627888574151202⟩, ⟨(-1930935903449386954), (-1930605832169741642)⟩, true⟩

def words07 : List Nat := [360582855067236641, 360582856611786653, 360582857855362359, 360582859263717362, 360582860301315288, 360582861339016775, 360582862741098707, 360582864066106547, 360582865116639186, 360582866167207107]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360628977964889829, 360628989360609867⟩, ⟨(-1977999364776549455), (-1977669056593096575)⟩, true⟩

def words08 : List Nat := [360582867633693944, 360582869521175530, 360582871375047569, 360582873228943793, 360582874615009958, 360582875693867641, 360582876926764512, 360582878159772900, 360582879099883631, 360582880175545563]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360619208633077350, 360619220034367136⟩, ⟨(-1558993652919870001), (-1558663105823373453)⟩, true⟩

def words09 : List Nat := [360582880822916775, 360582881470319748, 360582882474538264, 360582883752036209, 360582884737350987, 360582885722724563, 360582886409013073, 360582886712959364, 360582887560362904, 360582888407928980]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk428
