import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk011

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362320482072683734, 362320482077777031⟩, ⟨(-2042808103971108737), (-2042808100151345143)⟩, true⟩

def state01 : KState := ⟨⟨363232057099815932, 363232057105008716⟩, ⟨(-3057283547194698291), (-3057283543265000861)⟩, true⟩

def words00 : List Nat := [360466322120831151, 360467482790090677, 360469441887227015, 360471397438489149, 360472729529192017, 360474166178874302, 360475096851834147, 360476025846394747, 360477747606559896, 360480226733033018]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361732392254197779, 361732392259490390⟩, ⟨(-1387116155695044141), (-1387116151654024093)⟩, true⟩

def words01 : List Nat := [360482698349762901, 360485165525134919, 360486992652308485, 360488065608846751, 360488870690859792, 360489674331368028, 360491259509471018, 360492788906785193, 360493895695502434, 360495000509576007]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362846781082729015, 362846781088122451⟩, ⟨(-2639342743378728613), (-2639342739224274285)⟩, true⟩

def words02 : List Nat := [360496260155309679, 360498230394896607, 360500970801875203, 360503706337021188, 360505766239772468, 360507085420875930, 360508163081349425, 360509238832772721, 360511079548974863, 360513144713918849]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361470147511148961, 361470147516645221⟩, ⟨(-1075726286351307647), (-1075726282080151913)⟩, true⟩

def words03 : List Nat := [360514660880860938, 360516174371428313, 360517694969986975, 360519810166659773, 360521670550635894, 360523527662170547, 360524975900744412, 360525699507774069, 360526527970948583, 360527354981956219]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360488750122298665, 360488750127897841⟩, ⟨42782776958138997, 42782781347144639⟩, true⟩

def words04 : List Nat := [360528089183665902, 360528102376406665, 360528102376416456, 360527702642052455, 360527303605912594, 360526667988963468, 360526434069075347, 360526404394085880, 360526374770748672, 360525952546460576]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361240261989439645, 361240261995143092⟩, ⟨(-823393649622407584), (-823393645112952482)⟩, true⟩

def words05 : List Nat := [360526619042086307, 360527316647365970, 360528742897415466, 360529461170022485, 360529461170032859, 360529399371442172, 360529389308198265, 360529827443687688, 360530439887275600, 360531051275838224]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361645895274530403, 361645895280340446⟩, ⟨(-1298474676734491095), (-1298474672100861663)⟩, true⟩

def words06 : List Nat := [360531228680422580, 360531491781036115, 360532470067803186, 360533446675111128, 360534203110152231, 360534974274726820, 360535369479251675, 360535764007636573, 360536087868275594, 360537035611595048]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360117441086897098, 360117441092813450⟩, ⟨500781801891965404, 500781806650525666⟩, true⟩

def words07 : List Nat := [360538685832182283, 360540333239096268, 360541398559409410, 360541784131409452, 360541898206111382, 360542012086976594, 360542162105350895, 360542192413105848, 360542192413116036, 360541832454381693]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361266766593727256, 361266766599751156⟩, ⟨(-862658794374081390), (-862658789488076188)⟩, true⟩

def words08 : List Nat := [360541807535574314, 360542497917027908, 360542902853407493, 360543307106352085, 360543307106362559, 360543098945481443, 360542228439532712, 360542047520433764, 360541866905652917, 360542451915042444]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360410024807449545, 360410024813582716⟩, ⟨164900789080326801, 164900794096926879⟩, true⟩

def words09 : List Nat := [360542694324911058, 360542936328393889, 360543858332739734, 360545124163791249, 360546176434728076, 360547226947486462, 360547718110538412, 360547718110549905, 360547556751932417, 360547442141996822]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk011
