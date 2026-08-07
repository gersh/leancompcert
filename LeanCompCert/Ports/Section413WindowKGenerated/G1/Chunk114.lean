import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk114

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504604966180932, 362504606621817323⟩, ⟨(-209866081369162939), (-209853306156596895)⟩, true⟩

def state01 : KState := ⟨⟨362389584034554044, 362389585693193510⟩, ⟨1101987146801655126, 1101999956264984724⟩, true⟩

def words00 : List Nat := [371286206665996105, 371286206666332745, 371286203062020599, 371286198044577194, 371286193027888667, 371286190321106719, 371286183772490244, 371286178387488210, 371286173003312235, 371286167635022168]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362519294090622927, 362519295752303281⟩, ⟨(-378467913775833459), (-378455069600128465)⟩, true⟩

def words01 : List Nat := [371286159171318211, 371286158355908720, 371286163112975505, 371286163113314101, 371286161469921296, 371286158607812321, 371286155746069758, 371286155719123958, 371286156078583166, 371286158980602018]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362445920436171743, 362445922100900767⟩, ⟨459654003998822289, 459666883005443129⟩, true⟩

def words02 : List Nat := [371286161590081595, 371286161590418950, 371286154077354287, 371286154136522654, 371286156514968049, 371286156515305754, 371286150848915137, 371286145230308866, 371286139612554159, 371286137926185583]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362394163914902079, 362394165582679413⟩, ⟨1051420960569158789, 1051433874433372597⟩, true⟩

def words03 : List Nat := [371286134408282441, 371286132391627397, 371286130375209290, 371286127474997233, 371286114413645863, 371286103649893609, 371286092887853953, 371286089740607248, 371286082172416233, 371286074138136876]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486870127448386, 362486871798247451⟩, ⟨(-9459867417742530), (-9446918969435108)⟩, true⟩

def words04 : List Nat := [371286066105104956, 371286062942487331, 371286056593312771, 371286057221891715, 371286057222158134, 371286056170062183, 371286046355958821, 371286044144748920, 371286046739471952, 371286046811873385]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362446489076432894, 362446490750315649⟩, ⟨453239835332831412, 453252819105239406⟩, true⟩

def words05 : List Nat := [371286046812128393, 371286045203619759, 371286046933295609, 371286047285229047, 371286048993330503, 371286050701266965, 371286051731346077, 371286051731685493, 371286045058227132, 371286041607131115]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490733762232536, 362490735439133379⟩, ⟨(-53901914077859161), (-53888895702555163)⟩, true⟩

def words06 : List Nat := [371286041150165152, 371286041150506112, 371286037394159635, 371286033651897603, 371286029910156703, 371286028460023283, 371286029031288333, 371286033103277429, 371286037191554562, 371286037601481688]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362518588965557615, 362518590645531605⟩, ⟨(-373519209874433057), (-373506156234763475)⟩, true⟩

def words07 : List Nat := [371286045578598480, 371286053554503192, 371286061936540198, 371286061936879308, 371286060226793129, 371286056538678276, 371286054539736574, 371286054540109848, 371286055265678499, 371286058099914084]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362440954861036833, 362440956544070392⟩, ⟨517831640623735912, 517844729402946820⟩, true⟩

def words08 : List Nat := [371286060503326104, 371286060503665453, 371286052831018869, 371286052711202244, 371286054763487736, 371286054763827151, 371286046867209710, 371286037299011337, 371286027732336962, 371286025711120257]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362427625800026175, 362427627486114565⟩, ⟨671495287672591912, 671508411567547680⟩, true⟩

def words09 : List Nat := [371286025409560549, 371286029029634954, 371286032586511143, 371286032586856609, 371286029871103245, 371286027297707427, 371286029687668608, 371286029688008338, 371286024599534154, 371286019521903048]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk114
