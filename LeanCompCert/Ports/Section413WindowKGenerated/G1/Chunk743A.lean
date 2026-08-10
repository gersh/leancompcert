import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk743A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498328499664703, 362498410809337409⟩, ⟨(-981309701103612398), (-977179709995333002)⟩, true⟩

def state01 : KState := ⟨⟨362481458787154059, 362481541119879992⟩, ⟨272162466555878637, 276294170632932433⟩, true⟩

def words00 : List Nat := [371285259352473437, 371285259355028690, 371285259424076440, 371285259539236243, 371285259635334139, 371285259637890034, 371285259521159255, 371285259386196903, 371285259250211949, 371285259248942473]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 74300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 74300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473210578993785, 362473292934769484⟩, ⟨885199535352330083, 889332952376749647⟩, true⟩

def words01 : List Nat := [371285259331466271, 371285259465132937, 371285259581890735, 371285259584446691, 371285259486317772, 371285259425281139, 371285259479685522, 371285259482241341, 371285259359726888, 371285259201620625]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 74310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 74300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482933945121123, 362483016323768473⟩, ⟨162548514522219735, 166683631485712995⟩, true⟩

def words02 : List Nat := [371285259042354440, 371285259003781568, 371285258923523113, 371285258975692016, 371285258996971260, 371285258999571823, 371285258869998562, 371285258794269210, 371285258802374786, 371285258805020804]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 74320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 74300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485601705670761, 362485684107649640⟩, ⟨(-35781295114548397), (-31644443805191241)⟩, true⟩

def words03 : List Nat := [371285258776782362, 371285258750523288, 371285258723280196, 371285258718394946, 371285258644422674, 371285258626795720, 371285258608265694, 371285258580531637, 371285258432597054, 371285258441546075]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 74330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 74300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464069152982973, 362464151577699064⟩, ⟨1565091728778650608, 1569230270494241180⟩, true⟩

def words04 : List Nat := [371285258564047011, 371285258566603605, 371285258448221691, 371285258331041365, 371285258212861890, 371285258151053819, 371285257997714914, 371285257865477908, 371285257732435194, 371285257566542296]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 74340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 74300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk743A
