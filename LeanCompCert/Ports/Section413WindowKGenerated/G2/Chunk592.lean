import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360544386343956401, 360544408632406384⟩, ⟨2225751454422157330, 2226642875568567246⟩, true⟩

def state01 : KState := ⟨⟨360611104699414866, 360611126995675635⟩, ⟨(-1724331644089870952), (-1723439760507741974)⟩, true⟩

def words00 : List Nat := [360582020208480615, 360582019772333621, 360582019619227590, 360582019647670808, 360582019648433621, 360582019435843519, 360582019308838967, 360582019388597334, 360582019753465513, 360582020245907725]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589852526534185, 360589874830694027⟩, ⟨(-465966847656826695), (-465074496333790769)⟩, true⟩

def words01 : List Nat := [360582020522494020, 360582020799151648, 360582020928626374, 360582021228544438, 360582021371310848, 360582021514204409, 360582021514941546, 360582021514147066, 360582021494764604, 360582021628344628]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573438082693472, 360573460394644276⟩, ⟨506180054965024698, 507072867708637700⟩, true⟩

def words02 : List Nat := [360582022046886724, 360582022181345005, 360582022182083773, 360582022145579217, 360582022108936949, 360582021902399812, 360582021837398805, 360582021764487772, 360582021691489262, 360582021476320938]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620525202721665, 360620547522478919⟩, ⟨(-2283056931163354237), (-2282163656004022941)⟩, true⟩

def words03 : List Nat := [360582021386246700, 360582021440950702, 360582021780559851, 360582022127091323, 360582022187365497, 360582022247697439, 360582022472469541, 360582022838631862, 360582023489616468, 360582024140766862]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360618349502315832, 360618371829970753⟩, ⟨(-2154300708197139516), (-2153406965142655038)⟩, true⟩

def words04 : List Nat := [360582024566036698, 360582024868281762, 360582025455414220, 360582026042769906, 360582026417468302, 360582026749964666, 360582026894179735, 360582027038488564, 360582027407672679, 360582028022015737]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360591144121637483, 360591166457082482⟩, ⟨(-542127690830929202), (-541233486174052438)⟩, true⟩

def words05 : List Nat := [360582028864250692, 360582029706615992, 360582030405374169, 360582031139276898, 360582031679523100, 360582032219967123, 360582032802059461, 360582033100450055, 360582033255311106, 360582033410286545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601357395385197, 360601379738659502⟩, ⟨(-1147311019385384377), (-1146416350725280719)⟩, true⟩

def words06 : List Nat := [360582033688498651, 360582034213777976, 360582035023609013, 360582035833571579, 360582036400682150, 360582036684063331, 360582036947875652, 360582037211924939, 360582037467670120, 360582037794863628]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587711550215050, 360587733901379456⟩, ⟨(-338374995121392802), (-337479858777784600)⟩, true⟩

def words07 : List Nat := [360582037941048305, 360582038087318312, 360582038518175490, 360582039138462856, 360582039685396157, 360582040232460800, 360582040636052807, 360582040823641404, 360582040920354411, 360582041017339414]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597496887013621, 360597519245983805⟩, ⟨(-918586505682919003), (-917690906573990459)⟩, true⟩

def words08 : List Nat := [360582041398724999, 360582041496658295, 360582041497415975, 360582041373105095, 360582041248663191, 360582041006062567, 360582041091403801, 360582041237512964, 360582041240271734, 360582041502201883]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603769589219357, 360603791956005047⟩, ⟨(-1290515105781160513), (-1289619043252415617)⟩, true⟩

def words09 : List Nat := [360582041996820409, 360582042491675098, 360582043069831994, 360582043518464617, 360582043694587655, 360582043870771618, 360582043973474445, 360582044217695946, 360582044585108217, 360582044952695619]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk592
