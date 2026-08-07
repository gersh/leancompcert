import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360538805720037187, 360538814241243158⟩, ⟨1592825475562354462, 1593040328032508508⟩, true⟩

def state01 : KState := ⟨⟨360596287573017555, 360596296098972468⟩, ⟨(-551763685276610979), (-551548655647307481)⟩, true⟩

def words00 : List Nat := [360581521952652937, 360581520912240764, 360581520232881549, 360581519445779059, 360581518658683735, 360581517253707854, 360581515531092649, 360581514526481447, 360581513521776915, 360581513631184221]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587754808308896, 360587763339048408⟩, ⟨(-233331056982754482), (-233115848816137376)⟩, true⟩

def words01 : List Nat := [360581513665985881, 360581513700844165, 360581514453182600, 360581515566498103, 360581516254495001, 360581516942537074, 360581517082946830, 360581517083449922, 360581516933094272, 360581517101037205]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580005850380210, 360580014385853598⟩, ⟨55862274030959235, 56077658889416771⟩, true⟩

def words02 : List Nat := [360581517986134857, 360581518155707928, 360581518156165587, 360581517701753920, 360581517247275783, 360581516607223919, 360581516574346424, 360581516821773290, 360581516822221977, 360581516600128697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360642084290210353, 360642092830440606⟩, ⟨(-2262037898632812494), (-2261822336177505872)⟩, true⟩

def words03 : List Nat := [360581516560302084, 360581516498665425, 360581516778506686, 360581517014274893, 360581517014739674, 360581516634742972, 360581516590856390, 360581517497121152, 360581519119791907, 360581520742489628]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579539655593690, 360579548200617695⟩, ⟨73551252887363160, 73766994364393574⟩, true⟩

def words04 : List Nat := [360581522002138972, 360581522547079247, 360581523631444322, 360581524715898698, 360581525080947979, 360581525081451392, 360581524974709397, 360581524425479623, 360581523876185940, 360581523220547130]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360537561587622749, 360537570137392267⟩, ⟨1641777081146606627, 1641992999892256305⟩, true⟩

def words05 : List Nat := [360581523528749366, 360581523889915592, 360581523890364039, 360581523890342580, 360581523590211256, 360581522982103948, 360581522481166817, 360581522481670320, 360581521875405223, 360581520699487885]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360632811133433910, 360632819687956179⟩, ⟨(-1917194536844023314), (-1916978440512328822)⟩, true⟩

def words06 : List Nat := [360581519523519617, 360581519063538463, 360581519752735046, 360581520455463985, 360581520525345306, 360581520938780520, 360581521197922776, 360581521457201400, 360581522431868307, 360581523805038614]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613160278945058, 360613168838270143⟩, ⟨(-1182870824893632032), (-1182654549056882630)⟩, true⟩

def words07 : List Nat := [360581524817369642, 360581525829701552, 360581526600328311, 360581527730458572, 360581528326269619, 360581528922127998, 360581529160641975, 360581529292372214, 360581530139209376, 360581530986177988]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574769496295658, 360574778060362942⟩, ⟨252347894007664615, 252564347131732251⟩, true⟩

def words08 : List Nat := [360581532211459288, 360581532723552461, 360581532737572768, 360581532751646215, 360581532752067905, 360581532862132659, 360581533073701229, 360581533285350112, 360581533285802025, 360581532923886123]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360655409416441142, 360655417985263959⟩, ⟨(-2763247963418080853), (-2763031332461579927)⟩, true⟩

def words09 : List Nat := [360581533106400553, 360581533469699325, 360581534319542494, 360581535194035937, 360581535463745986, 360581535733476317, 360581536717542291, 360581538165819182, 360581540141622950, 360581542117440597]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373
