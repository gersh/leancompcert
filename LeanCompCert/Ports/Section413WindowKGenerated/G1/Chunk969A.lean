import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486058164233133, 362486201059568222⟩, ⟨(-94405960260561627), (-85057385303901273)⟩, true⟩

def state01 : KState := ⟨⟨362482739108166963, 362482882033798790⟩, ⟨227209418081891782, 236560928952024130⟩, true⟩

def words00 : List Nat := [371285323330782499, 371285323334198321, 371285323280191524, 371285323209218548, 371285323136913346, 371285323097932285, 371285323027668060, 371285323048424777, 371285323067598475, 371285323071142223]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499613110901246, 362499756067271983⟩, ⟨(-1408118773620898094), (-1398764283687365992)⟩, true⟩

def words01 : List Nat := [371285323129697157, 371285323215288129, 371285323401788683, 371285323467316186, 371285323517187893, 371285323568028395, 371285323684577989, 371285323759046293, 371285323910266080, 371285324063024324]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489967900556132, 362490110887671531⟩, ⟨(-473253700116227825), (-463896230256505721)⟩, true⟩

def words02 : List Nat := [371285324193271321, 371285324259051846, 371285324417097793, 371285324576869976, 371285324767747861, 371285324817695026, 371285324866393616, 371285324916306849, 371285324994653777, 371285325047947847]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488110343523627, 362488253361213887⟩, ⟨(-293143715593503416), (-283783281955401764)⟩, true⟩

def words03 : List Nat := [371285325206202764, 371285325365833842, 371285325523926114, 371285325573900708, 371285325654794623, 371285325737472293, 371285325879787737, 371285325913043610, 371285325945807436, 371285325979796784]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487298746548281, 362487441794713341⟩, ⟨(-214466683294104291), (-205103295272030173)⟩, true⟩

def words04 : List Nat := [371285326082164765, 371285326136543460, 371285326201830373, 371285326268490682, 371285326309744357, 371285326313145718, 371285326212190528, 371285326191429367, 371285326233671101, 371285326259079134]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969A
