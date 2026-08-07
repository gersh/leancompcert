import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594619108315873, 360594671129301997⟩, ⟨(-1123396849081753411), (-1120270347035419049)⟩, true⟩

def state01 : KState := ⟨⟨360585184058885050, 360585236092089261⟩, ⟨(-283757364634768868), (-280629775119507792)⟩, true⟩

def words00 : List Nat := [360582084002864286, 360582084004147427, 360582083955601520, 360582083995237562, 360582083996330033, 360582083949026359, 360582083803299619, 360582083594472045, 360582083385403202, 360582083338214802]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556754781413660, 360556806826721176⟩, ⟨2246884543468936539, 2250013210359379071⟩, true⟩

def words01 : List Nat := [360582083365398975, 360582083392857920, 360582083394001267, 360582083358193752, 360582083196169123, 360582082974582913, 360582082752624654, 360582082656913006, 360582082476774435, 360582082194170731]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585685637746706, 360585737695167162⟩, ⟨(-328675874996549709), (-325546129751713735)⟩, true⟩

def words02 : List Nat := [360582081911282205, 360582081754764596, 360582081679376483, 360582081623614294, 360582081567748822, 360582081404201539, 360582081243335320, 360582081183460749, 360582081123200024, 360582081147113656]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571943854173364, 360571995923836172⟩, ⟨894807975317702255, 897938810557248809⟩, true⟩

def words03 : List Nat := [360582081148257400, 360582081114470645, 360582081080457671, 360582081019768452, 360582081020842527, 360582081013179431, 360582081005392743, 360582080917435386, 360582080703290819, 360582080591519879]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568824301108709, 360568876382855475⟩, ⟨1172568821195160352, 1175700732450402100⟩, true⟩

def words04 : List Nat := [360582080491964344, 360582080493248015, 360582080394377123, 360582080219388499, 360582080044201524, 360582079788314989, 360582079630584317, 360582079470206830, 360582079309692941, 360582079086195738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360589083333463777, 360589135427321699⟩, ⟨(-631595150758539503), (-628462160944888525)⟩, true⟩

def words05 : List Nat := [360582078938973399, 360582078918028216, 360582078896708410, 360582078886850171, 360582078879791103, 360582078764053243, 360582078656918619, 360582078730391397, 360582078810666026, 360582078891229079]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561737487727302, 360561789593827804⟩, ⟨1803821393097601660, 1806955473297483750⟩, true⟩

def words06 : List Nat := [360582078892392905, 360582078876228803, 360582078733955877, 360582078547660565, 360582078361015868, 360582078123182898, 360582077759356954, 360582077300414964, 360582076841214803, 360582076508314135]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548958936419075, 360549011054610673⟩, ⟨2942106426423280391, 2945241583638003993⟩, true⟩

def words07 : List Nat := [360582076281590916, 360582076180981037, 360582076080242434, 360582075914895453, 360582075623509977, 360582075245632993, 360582074867380489, 360582074596908948, 360582074307059474, 360582073937228972]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565283873113154, 360565336003441165⟩, ⟨1487883463181999857, 1491019701567753885⟩, true⟩

def words08 : List Nat := [360582073567111744, 360582073300969138, 360582073136970393, 360582073099046153, 360582073061023022, 360582072916311412, 360582072645537660, 360582072500966515, 360582072356050562, 360582072109643520]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554260013851930, 360554312156423382⟩, ⟨2470052176044887597, 2473189505256020913⟩, true⟩

def words09 : List Nat := [360582071922947034, 360582071658091374, 360582071392996181, 360582071174044005, 360582071023885844, 360582070824059154, 360582070624076463, 360582070337276622, 360582069924437349, 360582069614394831]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890
