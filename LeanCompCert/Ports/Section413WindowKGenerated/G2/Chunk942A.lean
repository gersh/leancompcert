import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk942A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579557152291343, 360579615687848862⟩, ⟨228428498829805080, 232151908736810702⟩, true⟩

def state01 : KState := ⟨⟨360596873779388239, 360596932327786476⟩, ⟨(-1402870737665420032), (-1399146118097981046)⟩, true⟩

def words00 : List Nat := [360582080206864745, 360582080301892051, 360582080339865357, 360582080377983465, 360582080379125060, 360582080453289570, 360582080647077301, 360582080841124564, 360582080971761019, 360582081130812684]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609372698693228, 360609431259986517⟩, ⟨(-2580531096219919809), (-2576805261745584599)⟩, true⟩

def words01 : List Nat := [360582081323158791, 360582081515910583, 360582081678689975, 360582081816897624, 360582081841845146, 360582081866889893, 360582081973898136, 360582082153107119, 360582082444478550, 360582082736178178]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606106757973165, 360606165332270241⟩, ⟨(-2272915697857829217), (-2269188638103649017)⟩, true⟩

def words02 : List Nat := [360582082951468720, 360582083054634262, 360582083233978578, 360582083413727052, 360582083564632077, 360582083697946968, 360582083743975689, 360582083790130940, 360582083948567493, 360582084205697207]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576565229425422, 360576623816571192⟩, ⟨510979462007716934, 514707732558577188⟩, true⟩

def words03 : List Nat := [360582084447909777, 360582084690374317, 360582084866678924, 360582085073628024, 360582085236035724, 360582085398801738, 360582085526073062, 360582085541369948, 360582085542597778, 360582085486059293]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594369456982076, 360594428057035469⟩, ⟨(-1167028889222782840), (-1163299402197282164)⟩, true⟩

def words04 : List Nat := [360582085429227383, 360582085370162832, 360582085453599559, 360582085538313618, 360582085539572593, 360582085521646078, 360582085391248411, 360582085346087336, 360582085356385122, 360582085488763544]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk942A
