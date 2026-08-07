import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk308

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360539009785485462, 360539015504051993⟩, ⟨1360978594711398188, 1361097705791381950⟩, true⟩

def state01 : KState := ⟨⟨360519307794699412, 360519313517159011⟩, ⟨1967606704783738064, 1967725935789522438⟩, true⟩

def words00 : List Nat := [360583205553629106, 360583203595176838, 360583200585763604, 360583198626087131, 360583196666428773, 360583194204889989, 360583191031717861, 360583187000177737, 360583182968821223, 360583179986999632]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360513935003163859, 360513940729476641⟩, ⟨2133208121481217625, 2133327471223441281⟩, true⟩

def words01 : List Nat := [360583177914486652, 360583176006600687, 360583174098793996, 360583171667466395, 360583169594578503, 360583167256475583, 360583164918400617, 360583163629045191, 360583161906612335, 360583159661054300]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360525158710842774, 360525164441026628⟩, ⟨1787077611579526291, 1787197080647215899⟩, true⟩

def words02 : List Nat := [360583157415555792, 360583154541474338, 360583152448732208, 360583150662378809, 360583148876113252, 360583146164575973, 360583142403760076, 360583139205350509, 360583136007021060, 360583133856552000]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360506292932225628, 360506298666309302⟩, ⟨2368693118433537222, 2368812707751906134⟩, true⟩

def words03 : List Nat := [360583131976685665, 360583129447521437, 360583126918444936, 360583124554680478, 360583122741304573, 360583120197238666, 360583117653292013, 360583114444689437, 360583110907087359, 360583108416884916]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360534764126313437, 360534769864261180⟩, ⟨1490573432543554157, 1490693141049145253⟩, true⟩

def words04 : List Nat := [360583105926708652, 360583104483746412, 360583103080249751, 360583100972368470, 360583098864554721, 360583096321639186, 360583094459979579, 360583093431219839, 360583092402490193, 360583090549546404]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360606501276413047, 360606507018229156⟩, ⟨(-722949797528730580), (-722829969664869820)⟩, true⟩

def words05 : List Nat := [360583088983618161, 360583088464218483, 360583088471176158, 360583088471586155, 360583087951033899, 360583086295803153, 360583084640593246, 360583083668735353, 360583084141276548, 360583084900680637]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360628758244405035, 360628763990135250⟩, ⟨(-1410271151692221589), (-1410151203020497275)⟩, true⟩

def words06 : List Nat := [360583085093105364, 360583085093517334, 360583084991664435, 360583084863516526, 360583084735268632, 360583084342130183, 360583084306239318, 360583083748793810, 360583083678576119, 360583085158771819]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360530254918821157, 360530260668412413⟩, ⟨1631294538499559933, 1631414606380945205⟩, true⟩

def words07 : List Nat := [360583087683709709, 360583090208563484, 360583092050711669, 360583093274648951, 360583093789200175, 360583094303824093, 360583094304163910, 360583094256392687, 360583093162770161, 360583091452297807]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360564808022535930, 360564813776001324⟩, ⟨564318187112988923, 564438374646765279⟩, true⟩

def words08 : List Nat := [360583089741843679, 360583089076101388, 360583089545780790, 360583090152567626, 360583090152946317, 360583089827054724, 360583088455800425, 360583087809997613, 360583087164108424, 360583086303506885]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360559403276724788, 360559409034102365⟩, ⟨731313363821444821, 731433672222070047⟩, true⟩

def words09 : List Nat := [360583085712362734, 360583084302828124, 360583082893306400, 360583082809331368, 360583082809675269, 360583082563268663, 360583082316836659, 360583081535289171, 360583080792338854, 360583080026730911]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk308
