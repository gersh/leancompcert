import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk802

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551969133875153, 360552011036641409⟩, ⟨2416481774157100310, 2418751446090001178⟩, true⟩

def state01 : KState := ⟨⟨360592238860375195, 360592280773967676⟩, ⟨(-813440251675945185), (-811169711424856719)⟩, true⟩

def words00 : List Nat := [360582169657120953, 360582169247008445, 360582168914270548, 360582168706349323, 360582168498344401, 360582168157490666, 360582167887582291, 360582167773254021, 360582167698202463, 360582167825476511]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585641069559929, 360585682994088971⟩, ⟨(-284224826049927178), (-281953408524094850)⟩, true⟩

def words01 : List Nat := [360582167874904620, 360582167924464190, 360582167969938093, 360582168111359058, 360582168187874861, 360582168264576227, 360582168265609093, 360582168265052535, 360582168240719008, 360582168285863892]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572071752418909, 360572113687749355⟩, ⟨804366843034567133, 806639127103037769⟩, true⟩

def words02 : List Nat := [360582168485778564, 360582168530864290, 360582168531901286, 360582168436603775, 360582168341121051, 360582168205183221, 360582168147109704, 360582168052524820, 360582167957816839, 360582167771347798]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360612960940863446, 360613002887024853⟩, ⟨(-2476368862958572536), (-2474095709868049258)⟩, true⟩

def words03 : List Nat := [360582167676796382, 360582167707895210, 360582167893798806, 360582168162855500, 360582168300665682, 360582168438556989, 360582168574927583, 360582168805345052, 360582169190546003, 360582169576000962]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587526131224331, 360587568088330260⟩, ⟨(-435442761342280899), (-433168730009856443)⟩, true⟩

def words04 : List Nat := [360582169842047443, 360582170003093063, 360582170249000696, 360582170495251319, 360582170639222213, 360582170640369870, 360582170629425046, 360582170519972743, 360582170410287871, 360582170414407071]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360555648040000064, 360555690007906185⟩, ⟨2123010209511731627, 2125285107615577205⟩, true⟩

def words05 : List Nat := [360582170637679034, 360582170861165229, 360582170982714118, 360582170983861861, 360582170950406133, 360582170810578028, 360582170670407802, 360582170582975378, 360582170340482569, 360582170011738924]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577151620831780, 360577193599588926⟩, ⟨397089165356165823, 399364934415390963⟩, true⟩

def words06 : List Nat := [360582169682743424, 360582169473305243, 360582169459531089, 360582169530847621, 360582169531906521, 360582169470552537, 360582169303341551, 360582169160258509, 360582169016858317, 360582168869732385]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592774968292788, 360592816957996434⟩, ⟨(-857114471783333914), (-854837823997006116)⟩, true⟩

def words07 : List Nat := [360582168808785120, 360582168668043360, 360582168540201865, 360582168663451924, 360582168681479410, 360582168699706384, 360582168700729395, 360582168641360315, 360582168752588809, 360582168886547437]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598022027048240, 360598064027576735⟩, ⟨(-1278437755650609891), (-1276160238790437001)⟩, true⟩

def words08 : List Nat := [360582169118957291, 360582169230588391, 360582169231629288, 360582169224220253, 360582169216624252, 360582169200780406, 360582169386915852, 360582169573272049, 360582169640529640, 360582169839700256]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605801716181489, 360605843727545285⟩, ⟨(-1903137527065608093), (-1900859140185755241)⟩, true⟩

def words09 : List Nat := [360582170091121734, 360582170342871549, 360582170666549551, 360582170923083771, 360582171039804844, 360582171156611865, 360582171269253731, 360582171461253153, 360582171756979659, 360582172052968558]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk802
