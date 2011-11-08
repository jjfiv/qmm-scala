import scala.annotation.tailrec
import scala.collection.mutable.{Set => MutableSet}
import scala.collection.mutable.{Map => MutableMap}

object qmm {
    def bitcount(x: Int): Int = {
        @tailrec def bcrec(accum: Int, n: Int): Int = n match {
            case 0 => accum 
            case x => bcrec(accum + (x % 2),(x>>>1))
        }
        bcrec(0, x)
    }
    def genImplicants(zero_cubes: List[Implicant], order: Int): List[Implicant] = {

        //--- generate list and populate with zero-cubes
        var implicants = MutableSet[Implicant]()
        for(i <- zero_cubes) implicants += i
        
        //--- operate on current order until highest reached
        for(currentOrder <- 0 until order) {
            //--- grab all implicants of the current order
            val data = implicants.toList.filter(_.order == currentOrder)

            //println("Order " + currentOrder + "/" + order + "\n>>  "+data)

            for(List(a, b) <- data.combinations(2)) {
                if(a.canCombine(b)) {
                    a.prime = false
                    b.prime = false

                    //println("Can combine " + a + " and " + b)
                    val n = a.combine(b)
                    //println("Became: " + n)
                   
                    //n.print()

                    implicants += n
                }
            }
        }

        implicants.toList
   }

   def method(minterms: List[Int], dontcares: List[Int], vars: List[String]) {
        val implicants = (minterms:::dontcares).sorted.sortBy(bitcount(_)).map(new Implicant(_))
        val order = vars.length
        var table = new PrimeImplicantTable(minterms, genImplicants(implicants, order).filter(_.prime))

        table.solve()
        
        println(
            table.results.map(_.withVars(vars)).toList.sorted.reduceLeft(_ + " + " + _)
            )
   }

   def main(args: Array[String]) {
       method(List(0,1,2,3,4,7,6,8,11,13,15), Nil, List("A","B","C","D"))
       method(List(1,2,3,5,9,10,11,18,19,20,21,23,25,26,27),Nil,List("A","B","C","D","E"))

    }
}

class PrimeImplicantTable(minterms: List[Int], implicants: List[Implicant]) {

    //--- mutable class that slowly covers less and less
    class PrimeImplicant(val implicant: Implicant) {
        var terms = MutableSet[Int]()
        implicant.terms().map(terms += _)
        val tag = implicant.tag
        val order = implicant.order()
        var gateCost = 1

        //--- remove given terms from this data's effect
        def reduce(coveredTerms: MutableSet[Int]) = for(t <- coveredTerms) terms -= t
        //--- if this is higher order and contains all the minterms of the other
        def dominates(other: PrimeImplicant) = ((other.order <= order) && (other.terms.subsetOf(terms)))
        //--- whether this contains a given minterm or not
        def covers(minterm: Int) = terms.contains(minterm)
        //--- whether this is now empty
        def empty() = terms.size == 0

        override def equals(that: Any) = that match {
            case other: PrimeImplicant => hashCode == other.hashCode
            case _ => false
        }
        override def toString() = terms.mkString("",",","")
    }

    var rows = implicants.map(new PrimeImplicant(_))
    var cols = minterms.toSet
    var results = MutableSet[Implicant]()

    def solve() {
        //--- remove all don't cares from PI data
        for(row <- rows) {
            for(term <- row.terms) {
                if(!cols.contains(term)) {
                    row.terms -= term
                }
            }
        }

        var watchdog = 0
        while(watchdog < 10) {
            watchdog+=1
            reduceRows()
            if(selectEssential()) {
                watchdog = 0
            }
        }

        reduceRows()

        if(mintermsLeft) {
            println("TODO: Implement Branching Method")
            println("For now, select all remaining until done")
        }

        while(mintermsLeft) {
            selectRow(rows.toList(0))
        }
    }

    def selectRow(row: PrimeImplicant) {
        //--- remove it from the rows
        rows = rows.filter(_ != row)
        //--- remove the columns
        cols --= row.terms
        //--- go reduce all the remaining rows
        rows.map(_.reduce(row.terms))

        results += row.implicant
    }

    def selectEssential(): Boolean = {
        var done = false
        var effective = false

        while(!done) {
            done = true
            for(m <- cols) {
                implicantsForMinterm(m).filter(_ != ()) match {
                    case List(x: PrimeImplicant) => {
                        done = false
                        effective = true
                        //--- there's only one?
                        //println("Select " + x + " for minterm " + m)
                        selectRow(x)
                    }
                    case _ => ()
                }
            }
        }

        effective
    }

    def reduceRows() {
        //--- remove rows that cover nothing
        rows = rows.filter(!_.empty())
        //--- remove any term from a row that doesn't have a corresponding column

        var done = false
        while(!done) {
            for(List(rowA, rowB) <- rows.combinations(2)) {
                if(rowA dominates rowB) {
                    //println(rowA.implicant + " dominates " + rowB.implicant)
                    rows = rows.filter(_ != rowB)
                }
                else if(rowB dominates rowA) { 
                    //println(rowB.implicant + " dominates " + rowA.implicant)
                    rows = rows.filter(_ != rowA)
                }
            }
            done = true
        }
    }

    def mintermsLeft = cols.size != 0

    def implicantsForMinterm(minterm: Int) = {
        for( row <- rows ) yield {
            if( row.covers(minterm) ) row
        }
    }

    def print() {
        println("Prime Implicant table:")

        printf("%-16s |", "")
        for(col <- cols) {
            printf(" %2d |", col)
        }
        println() //newline
        printf("==================")
        for(col <- cols) {
            printf("=====")
        }
        println() //newline

        for(row <- rows) {
            printf("%-16s |", row)
            for(minterm <- cols) {
                if(row.covers(minterm)) printf("  X |")
                else                    printf("    |")
            }
            println(); //newline
        }
    }
}

class Implicant(val minterm: Int, val tag:Int=1, val group:List[Int]=Nil) {
    var prime: Boolean = true
  
    def order(): Int = {
      return group.length
    }
    def terms() = {
        var terms: List[Int] = List(minterm)
        for(difference <- group) {
          terms = terms ::: terms.map(_+difference)
        }
        terms
    }
    def canCombine(other: Implicant): Boolean = {
        //--- if the other one is less than this, don't bother comparing
        //if (other.minterm < minterm)
            //return false
  
        //--- only include ones that exist in at least one function
        if ((other.tag & tag) == 0)
            return false
  
        //--- if differences are not equivalent, don't bother comparing
        if (group != other.group)
            return false
  
        def bitdist(x: Int, y: Int) = qmm.bitcount(x ^ y)
  
            //--- difference needs to be just one bit
        if (bitdist(other.minterm,minterm) != 1) 
            return false
  
        return true
    }
    override def equals(that: Any) = that match {
        case other: Implicant => {
            hashCode == other.hashCode
        }
        case _ => false
    }
    override def hashCode = terms().hashCode
    def combine(other: Implicant): Implicant = {
        val newtag = other.tag & tag;
        val diff   = math.abs(other.minterm - minterm)
        val newgroup = (group ::: List(diff)).sorted
        val newmt  = if(minterm > other.minterm) other.minterm else minterm
  
        return new Implicant(newmt, newtag, newgroup)
    }
    override def toString() = terms().mkString("<",",",">")
    def printTerms() = println(terms().mkString("(",",",")"))
    def print() {
        printf("%d %s tag=%d %s\n", minterm, group.mkString("(",",",")"), tag, if (prime) {"prime"} else {""})
    }
    def withVars(vars: List[String]): String = {
        val weights = (0 until vars.length).map(1 << _).reverse
        val varByWeight = (weights zip vars).toMap
        //println(varByWeight)

        val expression = for (w <- weights) yield {
            if(!group.contains(w)) {
                if((minterm & w) != 0) {
                    varByWeight(w)
                } else {
                    varByWeight(w)+"'"
                }
            } else { "" }
        }

        expression.filter(_ != "").reduceLeft(_ + _)
    }
}

// vim: set ts=4 sw=4 et:
