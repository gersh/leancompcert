import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk039

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360431740572764398, 360431740647657384⟩, ⟨506086163158941366, 506086361565818426⟩, true⟩

def state01 : KState := ⟨⟨360524246542551865, 360524246617849472⟩, ⟨143185992193717432, 143186192180637314⟩, true⟩

def words00 : List Nat := [360561474686889367, 360561474686932253, 360561412223596324, 360561316618319454, 360561221062001562, 360561078073919237, 360560985008258799, 360560956705448784, 360560928417115068, 360560867127358587]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360974035805829143, 360974035881534038⟩, ⟨(-1618975863586647338), (-1618975662005193066)⟩, true⟩

def words01 : List Nat := [360560912996560249, 360560968201008330, 360560988387098504, 360560989261369328, 360560989261409488, 360560933166473436, 360560885515800820, 360560926500998212, 360561031886079285, 360561137217416417]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361089716789598420, 361089716865714573⟩, ⟨(-2074857895008008868), (-2074857691812358828)⟩, true⟩

def words02 : List Nat := [360561209685883061, 360561259093892027, 360561372774539302, 360561486397272889, 360561579239666971, 360561659177026117, 360561672504342400, 360561685824878338, 360561763254517279, 360561897559733307]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361031576376692649, 361031576453217015⟩, ⟨(-1844892178596279389), (-1844891973794272883)⟩, true⟩

def words03 : List Nat := [360562095880211204, 360562294099847763, 360562446593929440, 360562602490384644, 360562740717629835, 360562878874666716, 360563047694898052, 360563210884767109, 360563329759315756, 360563448573543259]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361301734953767072, 361301735030702502⟩, ⟨(-2910619614994352179), (-2910619408570731191)⟩, true⟩

def words04 : List Nat := [360563563213173670, 360563712221783804, 360563924817119430, 360564137304683713, 360564294322581266, 360564388842177025, 360564546900015916, 360564704877818490, 360564869357601610, 360565055858702824]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360981052992964682, 360981053070315602⟩, ⟨(-1641951755479694877), (-1641951547412824295)⟩, true⟩

def words05 : List Nat := [360565209244895273, 360565362553487352, 360565545186160025, 360565759547282697, 360565929951478290, 360566100269552383, 360566238252727695, 360566314109024268, 360566418841120679, 360566523520350234]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361027336413902032, 361027336491665366⟩, ⟨(-1825613594915824690), (-1825613385213689962)⟩, true⟩

def words06 : List Nat := [360566645010193751, 360566769440040632, 360566861798001991, 360566954109381416, 360567007118921372, 360567091544592673, 360567238784429798, 360567385950080214, 360567484253531048, 360567600056204855]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361002520018543374, 361002520096720680⟩, ⟨(-1728359352694843262), (-1728359141347210136)⟩, true⟩

def words07 : List Nat := [360567702448424310, 360567804789111947, 360567933729898362, 360568001139847530, 360568013857306476, 360568026568373969, 360568064688968177, 360568149867600412, 360568259005884611, 360568368089348862]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360863715403917093, 360863715482513106⟩, ⟨(-1177419062021529592), (-1177418849005342988)⟩, true⟩

def words08 : List Nat := [360568445519191987, 360568516782564667, 360568584145502863, 360568651474644780, 360568701681621512, 360568701681665437, 360568690761302228, 360568647489339112, 360568623039102572, 360568696978628029]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359908601615951922, 359908601694962903⟩, ⟨2639266091865636113, 2639266306539655711⟩, true⟩

def words09 : List Nat := [360568785790731903, 360568874558360000, 360568915892244281, 360568915892288289, 360568896317618050, 360568835025267064, 360568773763572793, 360568708913382770, 360568583266945164, 360568418271597817]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk039
