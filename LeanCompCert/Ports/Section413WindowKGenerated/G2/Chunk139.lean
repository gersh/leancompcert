import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk139

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360481030776168069, 360481031860776924⟩, ⟨1403394556387672525, 1403404766279558235⟩, true⟩

def state01 : KState := ⟨⟨360706856028633871, 360706857114876930⟩, ⟨(-1736421401247674863), (-1736411168632410893)⟩, true⟩

def words00 : List Nat := [360581988969490433, 360581988836210403, 360581995963910574, 360582003090619445, 360582005687577046, 360582006768510415, 360582013003748029, 360582019238139563, 360582025254982593, 360582034228770079]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360652528223947560, 360652529311836074⟩, ⟨(-980291628481730522), (-980281372969850018)⟩, true⟩

def words01 : List Nat := [360582040593204153, 360582046956742230, 360582058468917312, 360582072602745569, 360582082473959372, 360582092343784426, 360582099608048452, 360582101739620917, 360582106799213190, 360582111858135202]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360665424035194391, 360665425124714887⟩, ⟨(-1160131809431909760), (-1160121531194634264)⟩, true⟩

def words02 : List Nat := [360582122059410704, 360582127129053126, 360582127643549741, 360582128157986114, 360582128158131228, 360582130161509632, 360582135271020750, 360582140379830774, 360582142889702047, 360582148868078994]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360731485924039457, 360731487015193985⟩, ⟨(-2080597070378577183), (-2080586769371236223)⟩, true⟩

def words03 : List Nat := [360582159980795688, 360582171091969396, 360582187336001049, 360582198452801692, 360582205153970124, 360582211854191274, 360582215821415142, 360582223310923051, 360582234018646227, 360582244724872543]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360627970910203596, 360627972003009890⟩, ⟨(-637458819962917709), (-637448495921965397)⟩, true⟩

def words04 : List Nat := [360582252829485596, 360582255811373708, 360582262194597856, 360582268576959950, 360582273648119162, 360582276740636754, 360582277239914437, 360582277739140463, 360582277739281739, 360582280045736436]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360467886661824149, 360467887756264726⟩, ⟨1596534566263044231, 1596544913110702755⟩, true⟩

def words05 : List Nat := [360582283107396924, 360582286168649128, 360582286641103872, 360582286641277278, 360582282000802270, 360582276057273574, 360582270114546702, 360582265749869247, 360582261630511229, 360582253437719648]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360646227492118545, 360646228588196750⟩, ⟨(-894087292438503169), (-894076922721508949)⟩, true⟩

def words06 : List Nat := [360582245246063153, 360582239266954802, 360582238924446791, 360582241307691523, 360582241307854517, 360582239188004611, 360582231963152615, 360582229846278714, 360582228808293751, 360582233389376229]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591041795555966, 360591042893288129⟩, ⟨(-122681608704522971), (-122671215873412049)⟩, true⟩

def words07 : List Nat := [360582235391244904, 360582237392848805, 360582242765675596, 360582251822565981, 360582257630972003, 360582263438574218, 360582266664731444, 360582267500153104, 360582268128006645, 360582268755824900]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360525953196131862, 360525954295500941⟩, ⟨787077488577135581, 787087904300397983⟩, true⟩

def words08 : List Nat := [360582268755966683, 360582267779798284, 360582261707960201, 360582252381855952, 360582243057056686, 360582232443040792, 360582226200585760, 360582223339416008, 360582220478635710, 360582215046344430]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591474315346963, 360591475416358724⟩, ⟨(-130415021159269315), (-130404582446534655)⟩, true⟩

def words09 : List Nat := [360582211025275528, 360582208589163855, 360582206153351081, 360582203517241325, 360582195794196177, 360582183685124808, 360582171577750697, 360582164553259383, 360582160803143799, 360582161468608811]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk139
