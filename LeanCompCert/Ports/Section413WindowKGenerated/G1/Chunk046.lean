import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk046

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362337468554782920, 362337468802023989⟩, ⟨672146434414238243, 672147205368499183⟩, true⟩

def state01 : KState := ⟨⟨362550467365378245, 362550467613741860⟩, ⟨(-307702298607406330), (-307701522483699140)⟩, true⟩

def words00 : List Nat := [371283560367586383, 371283560367724747, 371283581764624879, 371283615918926367, 371283642440795519, 371283642440923053, 371283656141661526, 371283677201037957, 371283721079450834, 371283735555081332]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362422579918224635, 362422580167732879⟩, ⟨282719651675214917, 282720433081513939⟩, true⟩

def words01 : List Nat := [371283746253062447, 371283756946445966, 371283787297350434, 371283794438489059, 371283809132149002, 371283823819492088, 371283837138850483, 371283837138976194, 371283788315027871, 371283775066668272]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362210472780815210, 362210473031445192⟩, ⟨1264259066323370012, 1264259852917965744⟩, true⟩

def words02 : List Nat := [371283795153542438, 371283795153668407, 371283766438354212, 371283731366190076, 371283696309142843, 371283669949624430, 371283620569493303, 371283590883398606, 371283561210088552, 371283531315012788]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362580635922978324, 362580636174750073⟩, ⟨(-451852099035359440), (-451851307148529932)⟩, true⟩

def words03 : List Nat := [371283472351963121, 371283436247475124, 371283400158507508, 371283398151955934, 371283357870515411, 371283309374252022, 371283260898855784, 371283258663637257, 371283254427376359, 371283275410443129]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362570540233720680, 362570540486636521⟩, ⟨(-405644343426081985), (-405643546224846597)⟩, true⟩

def words04 : List Nat := [371283287174147989, 371283287174275370, 371283276729486703, 371283294580841470, 371283325870315082, 371283325870441923, 371283309340071641, 371283292647201619, 371283305315261031, 371283324071623654]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362553517491110575, 362553517745166426⟩, ⟨(-325632149025394487), (-325631346517189425)⟩, true⟩

def words05 : List Nat := [371283388832617564, 371283453565825095, 371283508309208521, 371283520699726781, 371283535043043551, 371283549380262190, 371283609637544332, 371283624775083240, 371283639773669787, 371283654765866450]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362557127423865317, 362557127679059784⟩, ⟨(-341034429857689101), (-341033622037687575)⟩, true⟩

def words06 : List Nat := [371283704226432594, 371283737301092757, 371283816167829194, 371283895000806607, 371283966669506829, 371283977428626736, 371284017209608241, 371284056973612561, 371284101207399808, 371284116841543688]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362595576508564455, 362595576764922202⟩, ⟨(-520441757425979398), (-520440944167719522)⟩, true⟩

def words07 : List Nat := [371284131971418231, 371284147094860605, 371284207849656029, 371284252601589493, 371284291596344128, 371284330574472228, 371284369413843989, 371284369413971500, 371284371434811459, 371284395191718246]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499189368001098, 362499189625497435⟩, ⟨(-69012027593176815), (-69011209000318647)⟩, true⟩

def words08 : List Nat := [371284454060829393, 371284454060956965, 371284452439037828, 371284439671398835, 371284427331208994, 371284427331350425, 371284433609498266, 371284454535659949, 371284475081866085, 371284478218761064]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362574533330830068, 362574533589482300⟩, ⟨(-422350179719015902), (-422349355699086470)⟩, true⟩

def words09 : List Nat := [371284526573070294, 371284574906837209, 371284644968060315, 371284654844157280, 371284657797456821, 371284660749539478, 371284665986928054, 371284665987070585, 371284672024297319, 371284691139854756]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk046
