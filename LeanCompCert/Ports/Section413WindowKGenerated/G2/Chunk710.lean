import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk710

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360624279273323413, 360624311799690874⟩, ⟨(-2978953201793798425), (-2977393322928773201)⟩, true⟩

def state01 : KState := ⟨⟨360598217346310069, 360598249882289375⟩, ⟨(-1128567430740443898), (-1127006869388717832)⟩, true⟩

def words00 : List Nat := [360582377702204743, 360582377982431750, 360582378255081088, 360582378528016116, 360582378671043741, 360582378755761466, 360582378756658498, 360582378742290440, 360582378780307151, 360582379004969119]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567901261969202, 360567933807421154⟩, ⟨1024416037449112990, 1025977271501697856⟩, true⟩

def words01 : List Nat := [360582379427180121, 360582379849572356, 360582380172779776, 360582380298095092, 360582380298952446, 360582380287497630, 360582380398161787, 360582380399168564, 360582380324514615, 360582380122142384]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579745355728594, 360579777910699744⟩, ⟨183252081991724001, 184813992143840881⟩, true⟩

def words02 : List Nat := [360582379919548873, 360582379731873928, 360582379878878654, 360582380051897596, 360582380054627272, 360582380055636885, 360582379992719412, 360582379951856470, 360582379910703302, 360582379825273077]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592810314365675, 360592842878921789⟩, ⟨(-744851342476424105), (-743288751455646165)⟩, true⟩

def words03 : List Nat := [360582379789539688, 360582379654926835, 360582379549188477, 360582379679203885, 360582379758961392, 360582379838898922, 360582379839805593, 360582379819108342, 360582379916744216, 360582380065174015]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579410401968032, 360579442976027165⟩, ⟨207069563707469508, 208632829869917748⟩, true⟩

def words04 : List Nat := [360582380300852549, 360582380338901888, 360582380339817438, 360582380207469985, 360582380074966183, 360582379834996343, 360582379693562231, 360582379645414653, 360582379597164700, 360582379398685433]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595728747902926, 360595761331468321⟩, ⟨(-952465924491892845), (-950901982862724681)⟩, true⟩

def words05 : List Nat := [360582379474787206, 360582379592510382, 360582379828690099, 360582379867297675, 360582379868235549, 360582379738048527, 360582379607686623, 360582379473367952, 360582379653198969, 360582379842566354]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586722458045085, 360586755051193521⟩, ⟨(-312577113182363342), (-311012490535501760)⟩, true⟩

def words06 : List Nat := [360582379932901426, 360582379933908832, 360582379879378458, 360582379933470820, 360582379934314275, 360582379907057312, 360582379681970245, 360582379358163572, 360582379034173137, 360582378969661877]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360538305908448520, 360538338511099386⟩, ⟨3128592151068264848, 3130157449100427690⟩, true⟩

def words07 : List Nat := [360582378970500509, 360582378870062301, 360582378769525870, 360582378548374347, 360582378129384586, 360582377660868364, 360582377192072462, 360582376710832336, 360582376234969312, 360582375616460957]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572224812806456, 360572257424967193⟩, ⟨717492207238226446, 719058181279751794⟩, true⟩

def words08 : List Nat := [360582374997741763, 360582374576849247, 360582374309227565, 360582374161272149, 360582374013254180, 360582373681206165, 360582373151358858, 360582372763021767, 360582372374399983, 360582372183460368]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360550985273103178, 360551017894889861⟩, ⟨2227530992097866573, 2229097650494139235⟩, true⟩

def words09 : List Nat := [360582372042088848, 360582371800126030, 360582371557966309, 360582371270215947, 360582371138446328, 360582370917486700, 360582370696427891, 360582370350371270, 360582369919079704, 360582369479284997]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk710
