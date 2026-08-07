import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk090

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360443434726127061, 360443435162102894⟩, ⟨1193697301101456035, 1193699961327021143⟩, true⟩

def state01 : KState := ⟨⟨360624855899319594, 360624856336311107⟩, ⟨(-439896360001625802), (-439893690629889772)⟩, true⟩

def words00 : List Nat := [360576053755827230, 360576051275035108, 360576049358521469, 360576041272118668, 360576033187494464, 360576021943990178, 360576027424392528, 360576036279723215, 360576036279822747, 360576038925299023]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360818689496700520, 360818689934709083⟩, ⟨(-2187280274364705323), (-2187277595824236901)⟩, true⟩

def words01 : List Nat := [360576056567510293, 360576074205837848, 360576104062717151, 360576121742286037, 360576128746634862, 360576135749440600, 360576150107098485, 360576171074788217, 360576197961667282, 360576224842610177]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360688335977501224, 360688336416538516⟩, ⟨(-1011901531739655350), (-1011898843914970566)⟩, true⟩

def words02 : List Nat := [360576243833688823, 360576259969043343, 360576275630485438, 360576291288486585, 360576301306866276, 360576301306974236, 360576299184365540, 360576287642344155, 360576276743776407, 360576289152236117]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360284214784105451, 360284215224159678⟩, ⟨2639800996232763277, 2639803693245630033⟩, true⟩

def words03 : List Nat := [360576303080871849, 360576317006443585, 360576324795315922, 360576324795423989, 360576320462752526, 360576308900146769, 360576297340069182, 360576285332416028, 360576261212901192, 360576228907040832]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598323811308253, 360598324252384139⟩, ⟨(-201032964562194843), (-201030258308535615)⟩, true⟩

def words04 : List Nat := [360576196608302855, 360576176462213926, 360576167512800922, 360576169110376829, 360576169110477480, 360576159803225928, 360576138395827262, 360576125206785544, 360576112020626987, 360576113418409050]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360612621728146800, 360612622170254592⟩, ⟨(-331104219186249430), (-331101503588580046)⟩, true⟩

def words05 : List Nat := [360576113418507123, 360576106328135086, 360576099239309441, 360576094344582971, 360576094344673767, 360576091859098525, 360576089374060367, 360576080781432122, 360576076750309289, 360576080783698078]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360506706375629494, 360506706818758152⟩, ⟨628371273841526891, 628373998693426481⟩, true⟩

def words06 : List Nat := [360576080783786606, 360576080179708147, 360576074669843363, 360576061330867310, 360576047994817552, 360576024881581995, 360576007943479884, 360576003090521600, 360575998238621749, 360575987303729864]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630498387301751, 360630498831456704⟩, ⟨(-495008211909681675), (-495005477744271573)⟩, true⟩

def words07 : List Nat := [360575979666238191, 360575979364319107, 360575985617305523, 360575989286185586, 360575989286286317, 360575981004568590, 360575972724655156, 360575976804848467, 360575982809566414, 360575988812984700]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360692117467988326, 360692117913178619⟩, ⟨(-1055714422980318750), (-1055711679408936210)⟩, true⟩

def words08 : List Nat := [360575988813082316, 360575988595111427, 360575986229361317, 360575988464766483, 360575988464857657, 360575986265664303, 360575986265761586, 360575981153933455, 360575978014329070, 360575990789714871]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360385246565963411, 360385247012180016⟩, ⟨1735963269545237538, 1735966022451007968⟩, true⟩

def words09 : List Nat := [360576015569290949, 360576040343437425, 360576055677067582, 360576059047447937, 360576059047539384, 360576054863464585, 360576050680278822, 360576048054490528, 360576033474582889, 360576012509152655]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk090
