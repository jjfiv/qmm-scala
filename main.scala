import scala.annotation.tailrec

object qmm {
    def bitcount(x: Int): Int = {
        @tailrec def bcrec(accum: Int, n: Int): Int = n match {
            case 0 => accum 
            case x => bcrec(accum + (x % 2),(x>>>1))
        }
        bcrec(0, x)
    }
    def genImplicants(zero_cubes: List[Implicant], order: Int): List[Implicant] = {

        import scala.collection.mutable.{Set => MutableSet}

        //--- generate list and populate with zero-cubes
        var implicants = MutableSet[Implicant]()
        for(i <- zero_cubes) implicants += i

        //--- operate on current order until highest reached
        for(currentOrder <- 0 until order) {
            //--- grab all implicants of the current order
            val data = implicants.toList.filter(_.order == currentOrder)

            for(List(a, b) <- data.combinations(2)) {
                if(a.canCombine(b)) {
                    a.prime = false
                    b.prime = false

                    val n = a.combine(b)

                    implicants += n
                }
            }
        }

        implicants.toList
    }

    def method(minterms: List[Int], dontcares: List[Int], vars: List[String]) {
        val implicants = (minterms:::dontcares).sorted.sortBy(bitcount(_)).map(new Implicant(_))
        val order = vars.length

        val prime_implicants = genImplicants(implicants, order).filter(_.prime)

        val results = PITable.solve(prime_implicants, minterms, vars)
        //println(results)

        println(results.toSumOfProducts(vars))
       
    }

    def main(args: Array[String]) {
        def letters(x: String): List[String] = x.split("").filter(_ != "").toList
        
        method(List(0,1,2,3,4,7,6,8,11,13,15), Nil, letters("ABCD"))
        method(List(1,2,3,5,9,10,11,18,19,20,21,23,25,26,27),Nil,letters("ABCDE"))
        //--- cyclic:
        method(List(8,10,16,18,19,20,21,23,25,27,29,40,42,43,46,47,55), Nil, letters("ABCDEF"))

        //--- don't cares
        method(List(1,4,7,14,17,20,21,22,23), List(0,3,6,19,30), letters("ABCDE"))
        //method(List(0,1,2,3),Nil,List("X","Y"))
    }
}


//--- class that slowly covers less and less
class PrimeImplicant(val implicant: Implicant, val terms: Set[Int]) {
    val tag = implicant.tag
    val order = implicant.order()

    //--- remove given terms from this data's effect
    def reduce(coveredTerms: Set[Int]) = { 
        new PrimeImplicant(implicant, terms -- coveredTerms)
    }
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
    //override def hashCode = implicant.hashCode
    override def toString() = terms.mkString("",",","")
}

object PITable {
    def solve(primeImplicants: List[Implicant], minterms: List[Int], vars: List[String]) = {
        
        val start = new PITable(
            primeImplicants.map(x => new PrimeImplicant(x, x.terms().toSet)),
            minterms.toSet,
            Set[Implicant](),
            vars
        )
        
        bestSolution(start)
    }
    //@tailrec
    def bestSolution(t: PITable): PITable = t.finished match {
        case true => t
        case false => {
            val branches = for(row <- t.rows) yield bestSolution(reduceTable(t.selectRow(row)))
            branches.minBy(_.cost(t.vars.length))
        }
    }
    @tailrec def reduceTable(t: PITable): PITable = t.selectEssential match {
        case (true, newTable) => reduceTable(newTable.reduceRows)
        case (false, _) => t.reduceRows
    }
}

case class PITable(val rows: List[PrimeImplicant], val cols: Set[Int], val results: Set[Implicant], val vars: List[String]) {

    def cost(order: Int) = {
        results.foldLeft(0){_ + _.cost(order)}
    }
    def finished = cols.size == 0
    def selectRow(row: PrimeImplicant) = {
        val nRows = rows.filter(_ != row).map(_.reduce(row.terms))
        val nCols = cols -- row.terms
        val nRes  = results + row.implicant
        this.copy(rows=nRows, cols=nCols, results=nRes)
    }

    def reduceRows = {
        var nRows = rows.filter(!_.empty())
        for(List(a,b) <- rows.combinations(2)) {
            if(a dominates b) {
                nRows = nRows.filter(_ != b)
            } else if(b dominates a) {
                nRows = nRows.filter(_ != a)
            }
        }
        this.copy(rows=nRows)
    }

    def rowsForMinterm(m: Int) = (for (row <- rows if row.covers(m)) yield row).filter(_ != ())

    def selectEssential = {
        var newTable = this
        var done = false
        var effective = false

        while(!done) {
            done = true
            for (m <- cols) {
                newTable.rowsForMinterm(m) match {
                    case List(x: PrimeImplicant) => {
                        done = false
                        effective = true
                        newTable = newTable.selectRow(x)
                    }
                    case _ => ()
                }
            }
        }

        (effective, newTable)
    }

    def toSumOfProducts(vars: List[String]) = {
        assert(finished)

        results.map(_.withVars(vars)).toList.sorted.reduceLeft(_ + " + " + _)
    }

}

class Implicant(val minterm: Int, val tag:Int=1, val group:List[Int]=Nil) {
    var prime: Boolean = true

    def cost(order: Int): Int = {
        order - group.size
    }

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
