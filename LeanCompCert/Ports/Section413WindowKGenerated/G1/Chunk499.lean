import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk499

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481843916280070, 362481879890090874⟩, ⟨154856038209753039, 156068800322291955⟩, true⟩

def state01 : KState := ⟨⟨362482750591085439, 362482786579809486⟩, ⟨109655298918034649, 110868805279119099⟩, true⟩

def words00 : List Nat := [371285007760400713, 371285007861900634, 371285008130721864, 371285008400210736, 371285008613154725, 371285008614819758, 371285008292998641, 371285008080197563, 371285007952631829, 371285007954389313]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485309032159482, 362485345036076725⟩, ⟨(-18059992956799947), (-16845728230222425)⟩, true⟩

def words01 : List Nat := [371285007911128094, 371285007852946715, 371285007929537003, 371285007931389999, 371285007949680931, 371285007997178620, 371285007998445823, 371285007965475319, 371285007579487436, 371285007588344704]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478708259425164, 362478744278164163⟩, ⟨311546297665777695, 312761302372581605⟩, true⟩

def words02 : List Nat := [371285007996841494, 371285007998507392, 371285007924691125, 371285007838698180, 371285007781333266, 371285007783169177, 371285007886494896, 371285008139672233, 371285008272080909, 371285008273805513]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498945223351790, 362498981257163544⟩, ⟨(-699069535719386231), (-697853778354808867)⟩, true⟩

def words03 : List Nat := [371285008185704147, 371285008223901189, 371285008416862660, 371285008418528896, 371285008077568102, 371285007668695734, 371285007259141375, 371285007250739837, 371285007411115036, 371285007692790488]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493432225383065, 362493468274225623⟩, ⟨(-423798971378575159), (-422582463298973921)⟩, true⟩

def words04 : List Nat := [371285007978656808, 371285007980323521, 371285007883138445, 371285008036151880, 371285008200253313, 371285008201932690, 371285008097933724, 371285007995028050, 371285008162926653, 371285008334218437]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465879081061636, 362465915144946031⟩, ⟨952670857513861814, 953888117010049862⟩, true⟩

def words05 : List Nat := [371285008631389576, 371285008929270873, 371285009227115159, 371285009228782230, 371285008992871235, 371285008818961124, 371285008868435219, 371285008870102477, 371285008562002390, 371285008181715648]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495054096504482, 362495090175317609⟩, ⟨(-505028292392391244), (-503810286981014890)⟩, true⟩

def words06 : List Nat := [371285007800688752, 371285007758912022, 371285007649136331, 371285007723410768, 371285007729054678, 371285007730752036, 371285007491295760, 371285007523183349, 371285007918494931, 371285008121987057]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473498789434464, 362473534883444271⟩, ⟨572234147051991736, 573452911916873120⟩, true⟩

def words07 : List Nat := [371285008325642103, 371285008529846011, 371285008745632960, 371285008761772593, 371285008894725123, 371285009028323332, 371285009159270984, 371285009160938948, 371285008758623252, 371285008531141688]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362453035471840102, 362453071580700894⟩, ⟨1595156664263638777, 1596376171458463195⟩, true⟩

def words08 : List Nat := [371285008422422248, 371285008424090587, 371285008071177228, 371285007719547016, 371285007367262550, 371285007088312173, 371285006609615703, 371285006241211723, 371285005872278104, 371285005490912106]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493383486050772, 362493419610006511⟩, ⟨(-422020734497875158), (-420800472630093518)⟩, true⟩

def words09 : List Nat := [371285004853251309, 371285004616006431, 371285004538154320, 371285004539851726, 371285004368689325, 371285004054810008, 371285003740282287, 371285003660303853, 371285003598655549, 371285003768870732]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk499
