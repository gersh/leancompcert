import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk429A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360619208633077350, 360619220034367136⟩, ⟨(-1558993652919870001), (-1558663105823373453)⟩, true⟩

def state01 : KState := ⟨⟨360641834464547933, 360641845871348130⟩, ⟨(-2529812796110583850), (-2529482012589537274)⟩, true⟩

def words00 : List Nat := [360582889798811522, 360582890953400055, 360582891668147533, 360582892382911576, 360582892957150834, 360582893802861203, 360582895068874381, 360582896334942014, 360582897326975848, 360582898701331362]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360643404052812940, 360643415465131762⟩, ⟨(-2597303225379657227), (-2596972205026836027)⟩, true⟩

def words01 : List Nat := [360582899992239564, 360582901283261541, 360582902728350638, 360582903839723407, 360582904494155672, 360582905148603105, 360582905787839374, 360582906780135225, 360582908190410048, 360582909600752395]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360657205173355095, 360657216591253512⟩, ⟨(-3189898430538509296), (-3189567170683214800)⟩, true⟩

def words02 : List Nat := [360582910669024652, 360582911659630380, 360582913193002866, 360582914726486628, 360582915890991141, 360582916959471593, 360582917679194696, 360582918398947933, 360582919661376430, 360582921392663142]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360614939102335470, 360614950525751013⟩, ⟨(-1375254062521244764), (-1374922565787459822)⟩, true⟩

def words03 : List Nat := [360582923108747913, 360582924824856566, 360582926130581006, 360582926896632175, 360582927436723080, 360582927976943295, 360582929059626320, 360582930156982127, 360582930903211223, 360582931649483869]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360660161206216791, 360660172635156097⟩, ⟨(-3317273996729976515), (-3316942262778275411)⟩, true⟩

def words04 : List Nat := [360582932643536421, 360582934023126506, 360582935944987993, 360582937866876013, 360582939272210720, 360582940261672407, 360582941626866759, 360582942992174913, 360582944642400832, 360582946441056350]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk429A
