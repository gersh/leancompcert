import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk178

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362441778745050720, 362441782943748018⟩, ⟨779253123102009462, 779303674638398448⟩, true⟩

def state01 : KState := ⟨⟨362475482073793004, 362475486277398181⟩, ⟨179225403844288369, 179276042765768107⟩, true⟩

def words00 : List Nat := [371285561589968463, 371285560431137144, 371285558028431475, 371285557889899154, 371285557751217377, 371285557122158300, 371285553148791002, 371285552324846670, 371285552309550204, 371285552310119449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478263823069907, 362478268031656576⟩, ⟨129736713412390259, 129787441078823625⟩, true⟩

def words01 : List Nat := [371285551745374500, 371285551155023194, 371285552566502428, 371285552992516632, 371285553583196534, 371285554174018793, 371285554764517761, 371285554765065840, 371285551685561151, 371285551277508362]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479896532445381, 362479900745916791⟩, ⟨100855994435390459, 100906809173491861⟩, true⟩

def words02 : List Nat := [371285553100175886, 371285553470097287, 371285553834421617, 371285554198895095, 371285554871888372, 371285554872491747, 371285556210090980, 371285558449619466, 371285560128926235, 371285560129493544]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362551233920762300, 362551238139195543⟩, ⟨(-1171576645772900344), (-1171525742540201448)⟩, true⟩

def words03 : List Nat := [371285561128300194, 371285562444633855, 371285565732330767, 371285565732879527, 371285565448509855, 371285564396333665, 371285565428946671, 371285565973698952, 371285569655246823, 371285573336631775]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487581277220274, 362487585500608447⟩, ⟨(-35824390834934174), (-35773399180975632)⟩, true⟩

def words04 : List Nat := [371285576932470279, 371285577717570650, 371285579797513054, 371285581877492492, 371285584684453228, 371285584685002105, 371285583314686584, 371285581995115002, 371285581387971508, 371285581500878406]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362433411929051575, 362433416157372978⟩, ⟨931682835722241865, 931733915459339101⟩, true⟩

def words05 : List Nat := [371285584746615633, 371285587992206537, 371285590578738157, 371285590579287268, 371285589589732873, 371285589545172661, 371285590750418135, 371285590750967259, 371285587830172292, 371285584909638339]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477583141799307, 362477587375034770⟩, ⟨142788466896613578, 142839634424075878⟩, true⟩

def words06 : List Nat := [371285581989192333, 371285581633322754, 371285581715621877, 371285583321165029, 371285584405219220, 371285584405768670, 371285581322394771, 371285580209958810, 371285580638843542, 371285580639412167]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468358244977643, 362468362483231373⟩, ⟨307681318657786026, 307732575886927356⟩, true⟩

def words07 : List Nat := [371285580192555291, 371285578894966915, 371285578961252174, 371285578961863230, 371285578751870435, 371285578516151421, 371285578280278672, 371285577652853192, 371285574439361706, 371285573477408495]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362437321232064447, 362437325475214481⟩, ⟨862904369994300387, 862955714794783731⟩, true⟩

def words08 : List Nat := [371285574673860789, 371285574674410739, 371285572674033435, 371285570644001742, 371285568613997582, 371285566719690755, 371285563778930565, 371285563364998081, 371285562950916382, 371285562239596526]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497186525671671, 362497190773794166⟩, ⟨(-208227713184909685), (-208176279401808043)⟩, true⟩

def words09 : List Nat := [371285559965588889, 371285560387975525, 371285563100362411, 371285563100913536, 371285562488741907, 371285561387849577, 371285560808061162, 371285560808668330, 371285560813437834, 371285561463733175]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk178
