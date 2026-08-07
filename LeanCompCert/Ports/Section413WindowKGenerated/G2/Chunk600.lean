import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk600

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602415087370459, 360602438006732812⟩, ⟨(-1214891155669101161), (-1213962131564738441)⟩, true⟩

def state01 : KState := ⟨⟨360601782633496210, 360601805560763430⟩, ⟨(-1176986667017274858), (-1176057168581509680)⟩, true⟩

def words00 : List Nat := [360582206128307520, 360582206495296566, 360582206695627823, 360582206896051689, 360582206916720135, 360582207098166153, 360582207407320908, 360582207716629384, 360582207873363322, 360582208200803065]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360635461443618295, 360635484378817698⟩, ⟨(-3198316254464527272), (-3197386279978258074)⟩, true⟩

def words01 : List Nat := [360582208519806304, 360582208839042169, 360582209435715187, 360582209877322574, 360582210083374480, 360582210289491511, 360582210773115203, 360582211475688536, 360582212363953413, 360582213252378981]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610338532173477, 360610361475377804⟩, ⟨(-1690483527023593067), (-1689553072044914367)⟩, true⟩

def words02 : List Nat := [360582213948251987, 360582214367639429, 360582215009741947, 360582215652070148, 360582216105083624, 360582216281682972, 360582216282438137, 360582216205809800, 360582216329114065, 360582216798926556]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607106155185279, 360607129106308517⟩, ⟨(-1496370968317532816), (-1495440037926000090)⟩, true⟩

def words03 : List Nat := [360582217487136341, 360582218175498971, 360582218724234319, 360582219192472350, 360582219589671896, 360582219987080948, 360582220661696630, 360582221294113499, 360582221709735397, 360582222125446673]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360630944567793320, 360630967526844964⟩, ⟨(-2927643009790488676), (-2926711603337346138)⟩, true⟩

def words04 : List Nat := [360582222818390340, 360582223649801122, 360582224681268842, 360582225712865538, 360582226509166619, 360582227311491422, 360582228093351152, 360582228875437213, 360582229614178422, 360582230426657834]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360593864298770728, 360593887265836632⟩, ⟨(-700769979190421785), (-699838091443318199)⟩, true⟩

def words05 : List Nat := [360582231055224900, 360582231683862583, 360582232220038620, 360582232894551480, 360582233497962596, 360582234101490897, 360582234565935048, 360582234754279744, 360582234948975659, 360582235143969808]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578203821699015, 360578226796665246⟩, ⟨239851820439630121, 240784182720863023⟩, true⟩

def words06 : List Nat := [360582235431080108, 360582235536672611, 360582235537421202, 360582235503613319, 360582235469669640, 360582235318445265, 360582235321691096, 360582235325086138, 360582235325834818, 360582235189918465]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608221356270956, 360608244339172805⟩, ⟨(-1563572878471682224), (-1562640039459872662)⟩, true⟩

def words07 : List Nat := [360582235123875259, 360582235009700367, 360582234895285860, 360582234862355014, 360582234845561873, 360582234588968461, 360582234351923383, 360582234583141986, 360582235016740338, 360582235450514829]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620827322792173, 360620850313709756⟩, ⟨(-2321144412243171667), (-2320211091605860935)⟩, true⟩

def words08 : List Nat := [360582235673169884, 360582235853353363, 360582236310435137, 360582236767757075, 360582237116190264, 360582237383980760, 360582237512400183, 360582237640923134, 360582238046290442, 360582238689812570]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572972614485019, 360572995613317786⟩, ⟨554785452738686217, 555719249039123405⟩, true⟩

def words09 : List Nat := [360582239610050497, 360582240530419139, 360582241237102441, 360582241668053538, 360582241830462729, 360582241993075306, 360582242274598700, 360582242342071135, 360582242342825000, 360582242189840900]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk600
