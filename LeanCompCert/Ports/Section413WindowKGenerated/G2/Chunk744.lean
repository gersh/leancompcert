import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk744

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360573195972934496, 360573231821979373⟩, ⟨674261618221627009, 676063102731001713⟩, true⟩

def state01 : KState := ⟨⟨360565763171159211, 360565799030183210⟩, ⟨1227244082969612757, 1229046309975735531⟩, true⟩

def words00 : List Nat := [360582318571767326, 360582318572825651, 360582318394722285, 360582318077406290, 360582317759918069, 360582317348252748, 360582317027355121, 360582316810547642, 360582316593633101, 360582316249777025]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592567190167818, 360592603059178232⟩, ⟨(-767381232577423525), (-765578262433765197)⟩, true⟩

def words01 : List Nat := [360582316028659994, 360582315988196851, 360582316086075678, 360582316130282226, 360582316131265578, 360582315987536557, 360582315843623662, 360582315696029664, 360582315793067055, 360582315932393672]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593801542552640, 360593837421656320⟩, ⟨(-859388843503159576), (-857585122169434010)⟩, true⟩

def words02 : List Nat := [360582315980508263, 360582315981566880, 360582315890170877, 360582315878758537, 360582315867050912, 360582315748673859, 360582315687789639, 360582315536790369, 360582315385590925, 360582315540690467]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360562441070606956, 360562476959689768⟩, ⟨1474901130242094671, 1476705594372948967⟩, true⟩

def words03 : List Nat := [360582315657902678, 360582315775298655, 360582315783076802, 360582315784135513, 360582315611527879, 360582315393732312, 360582315175637881, 360582314925838762, 360582314753222567, 360582314487824816]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584349028592094, 360584384927667556⟩, ⟨(-156042501851192307), (-154237293818151275)⟩, true⟩

def words04 : List Nat := [360582314222194245, 360582314158674623, 360582314161925323, 360582314165376236, 360582314166369884, 360582313999851108, 360582313652839752, 360582313454656625, 360582313256148822, 360582313265852159]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360568436929853698, 360568472839026486⟩, ⟨1028753825899339381, 1030559785728113787⟩, true⟩

def words05 : List Nat := [360582313266801743, 360582313160833552, 360582313127727536, 360582313292949308, 360582313412464541, 360582313532149750, 360582313560774178, 360582313561833536, 360582313472066345, 360582313287397801]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576617441555182, 360576653360704832⟩, ⟨419533440324969599, 421340143080070303⟩, true⟩

def words06 : List Nat := [360582313102380886, 360582312997230203, 360582312785411750, 360582312483582276, 360582312181583405, 360582311810786674, 360582311575139907, 360582311488359585, 360582311401466285, 360582311211424318]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585411994686539, 360585447923846729⟩, ⟨(-235448355067454215), (-233640906778509667)⟩, true⟩

def words07 : List Nat := [360582311240367830, 360582311345594414, 360582311446568628, 360582311463456012, 360582311464443445, 360582311324227108, 360582311183817720, 360582311006084477, 360582310961036780, 360582311004272898]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571916539832241, 360571952479076802⟩, ⟨769625437437926419, 771433636861407091⟩, true⟩

def words08 : List Nat := [360582311005224058, 360582310882632757, 360582310627168999, 360582310518925122, 360582310410392457, 360582310256662422, 360582309922771996, 360582309449568628, 360582308976175087, 360582308683088904]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554963076745381, 360554999025968463⟩, ⟨2032673719472885119, 2034482662245847531⟩, true⟩

def words09 : List Nat := [360582308548636921, 360582308553421182, 360582308554375992, 360582308452012960, 360582308428406657, 360582308332296321, 360582308235879177, 360582308139860872, 360582307883542497, 360582307518079146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk744
