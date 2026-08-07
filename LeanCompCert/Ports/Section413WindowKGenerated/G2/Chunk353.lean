import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360657718695116936, 360657726292617446⟩, ⟨(-2674828966256110423), (-2674647653412643915)⟩, true⟩

def state01 : KState := ⟨⟨360613476307426962, 360613483909445296⟩, ⟨(-1113026236194355807), (-1112844763850024543)⟩, true⟩

def words00 : List Nat := [360581960838738357, 360581961960421065, 360581963575055366, 360581965189736692, 360581966359750782, 360581966965992991, 360581967172096005, 360581967378245615, 360581967489648023, 360581968382729825]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560320040709730, 360560327647181811⟩, ⟨764333803381255778, 764515433010357898⟩, true⟩

def words01 : List Nat := [360581970076383792, 360581971770032521, 360581972988266210, 360581973407740356, 360581973408143775, 360581973269748607, 360581973792933419, 360581973793407365, 360581973656856128, 360581973044492411]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594341272686890, 360594348883639700⟩, ⟨(-437469662446394168), (-437287874535879870)⟩, true⟩

def words02 : List Nat := [360581972432061408, 360581971373546925, 360581971408448833, 360581971826384138, 360581971826825597, 360581971540844259, 360581971246324046, 360581971499543113, 360581971643564254, 360581971994377130]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590644433525884, 360590652048992121⟩, ⟨(-306839507730902149), (-306657560339150799)⟩, true⟩

def words03 : List Nat := [360581971994799390, 360581971940665282, 360581972414216247, 360581973464789471, 360581974113381138, 360581974762021418, 360581975005930698, 360581975006404848, 360581974698129410, 360581974944203373]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590198769743941, 360590206389681686⟩, ⟨(-291204661133023100), (-291022555696358322)⟩, true⟩

def words04 : List Nat := [360581975702174988, 360581976018861574, 360581976019299626, 360581975513938573, 360581975008528646, 360581974302568145, 360581974127831521, 360581974158555051, 360581974158977500, 360581974018441938]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360616031753057009, 360616039377471106⟩, ⟨(-1204585901030675280), (-1204403637332488952)⟩, true⟩

def words05 : List Nat := [360581974178578513, 360581974338848697, 360581975297980855, 360581976139955228, 360581976301579938, 360581976463232680, 360581976602973644, 360581977224457336, 360581978188137985, 360581979151874192]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588002275060386, 360588009903992245⟩, ⟨(-213564019054204886), (-213381595585440664)⟩, true⟩

def words06 : List Nat := [360581979716806511, 360581979717280974, 360581980051885052, 360581980618778154, 360581980661890153, 360581980662364672, 360581979908939868, 360581978751714390, 360581977594463624, 360581977233285015]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545645027599554, 360545652661008452⟩, ⟨1284751776760927685, 1284934358604335065⟩, true⟩

def words07 : List Nat := [360581977233675739, 360581977164565714, 360581977095409522, 360581976517101465, 360581975582032668, 360581974439146465, 360581973296183516, 360581972414788392, 360581971786512527, 360581970760460243]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597988213384066, 360597995851270592⟩, ⟨(-567330400433519725), (-567147660148815715)⟩, true⟩

def words08 : List Nat := [360581969734358191, 360581969675789062, 360581970308272502, 360581970940810857, 360581970941256007, 360581970804539617, 360581970444689523, 360581970200311114, 360581970203416994, 360581970656725403]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586840905569420, 360586848547985034⟩, ⟨(-172660984033961793), (-172478083442734033)⟩, true⟩

def words09 : List Nat := [360581970657148590, 360581970638491779, 360581971397751921, 360581972756827126, 360581973915628268, 360581975074441428, 360581975669746930, 360581976147167842, 360581976285198865, 360581976423371528]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk353
