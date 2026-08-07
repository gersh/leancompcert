import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476912417707795, 362477055619308602⟩, ⟨792933705272846634, 802311972733328328⟩, true⟩

def state01 : KState := ⟨⟨362495469602369258, 362495612834439861⟩, ⟨(-1007167572943592138), (-997786349760805288)⟩, true⟩

def words00 : List Nat := [371285326814943600, 371285326818740150, 371285326883999560, 371285326972343220, 371285327034187582, 371285327041218103, 371285327153479246, 371285327267553678, 371285327434051689, 371285327543599021]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491502312261495, 362491645575393342⟩, ⟨(-622258872374019009), (-612874635794400663)⟩, true⟩

def words01 : List Nat := [371285327651740758, 371285327760974072, 371285327912861655, 371285328032476746, 371285328182641960, 371285328334140249, 371285328487436110, 371285328510892314, 371285328578328738, 371285328647761238]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485400952395138, 362485544245781824⟩, ⟨(-30249348407442940), (-20862176344618516)⟩, true⟩

def words02 : List Nat := [371285328821552462, 371285328864330806, 371285328905871728, 371285328948611781, 371285329022730066, 371285329048589609, 371285329110032856, 371285329172790316, 371285329234768416, 371285329240511915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502468319135446, 362502611643346254⟩, ⟨(-1686395733652928806), (-1677005570572090004)⟩, true⟩

def words03 : List Nat := [371285329299274578, 371285329359837292, 371285329496567434, 371285329564141089, 371285329614695877, 371285329666290038, 371285329792731826, 371285329868283190, 371285330048680899, 371285330230638511]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494146679294724, 362494290034237913⟩, ⟨(-878850913609147946), (-869457768097660634)⟩, true⟩

def words04 : List Nat := [371285330390719105, 371285330458518465, 371285330616178198, 371285330775564235, 371285330953878986, 371285330991607838, 371285331017690360, 371285331044993765, 371285331166174051, 371285331262374690]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481265638401955, 362481409023979719⟩, ⟨371329569426681086, 380725688177558400⟩, true⟩

def words05 : List Nat := [371285331414544426, 371285331568072685, 371285331687408071, 371285331690813619, 371285331668449471, 371285331642267680, 371285331675434981, 371285331678857053, 371285331641349872, 371285331604735722]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486184004790458, 362486327420865919⟩, ⟨(-106038135845095968), (-96639056828649080)⟩, true⟩

def words06 : List Nat := [371285331603832280, 371285331607651341, 371285331685457843, 371285331766152303, 371285331828971991, 371285331832378039, 371285331771001005, 371285331792719484, 371285331856839238, 371285331870631260]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487045004130086, 362487188451263600⟩, ⟨(-189606812107335429), (-180204718124535219)⟩, true⟩

def words07 : List Nat := [371285331878584822, 371285331887716646, 371285332001658154, 371285332064009177, 371285332126914265, 371285332191137910, 371285332253835865, 371285332257242330, 371285332197339599, 371285332220712571]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483569651484604, 362483713129016904⟩, ⟨147795131360574525, 157200176611836751⟩, true⟩

def words08 : List Nat := [371285332348363817, 371285332351770347, 371285332338255450, 371285332295950378, 371285332252353507, 371285332242053885, 371285332207522752, 371285332226289177, 371285332243522855, 371285332247119818]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491768477425336, 362491911985685814⟩, ⟨(-648249045474472257), (-638841016670116363)⟩, true⟩

def words09 : List Nat := [371285332311303885, 371285332393941954, 371285332570148012, 371285332623867053, 371285332660643103, 371285332698511703, 371285332727319158, 371285332731074283, 371285332774710093, 371285332846267373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk970
