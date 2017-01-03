import copy
import ply.lex as lex
import ply.yacc as yacc

inFile = 'input.txt'
outFile = 'output.txt'


global MAXKB
MAXKB = 10000

tokens = (
    'IMPLY',
    'LPAREN',
    'RPAREN',
    'OR',
    'AND',
    'NOT',
    'PREDIC',
    'CONST',
    'VAR',
        )

t_IMPLY = r'\=>'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_OR = r'\|'
t_AND = r'\&'
t_NOT = r'~'
t_PREDIC = r'[A-Z][A-Za-z]*\([A-Z]?[A-Za-z]+[,A-Z?A-Za-z*]*\)' # r'[A-Z][a-z]*\([A-Za-z][a-z]*(?:,[A-Za-z][a-z]*)*\)'
t_CONST = r'[A-Z][A-Za-z]*'
t_VAR = r'[a-z]'
t_ignore = ' \t'

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_error(t):
    t.lexer.skip(1)

#yacc
precedence = (
    ('left', 'IMPLY'),
    ('left', 'AND'),
    ('left', 'OR'),
    ('right', 'NOT'),
)

def p_expression_and(p):
    'expression : LPAREN expression AND expression RPAREN'
    p[0] = '(' + p[2] + '&' + p[4] + ')'

def p_expression_or(p):
    'expression : LPAREN expression OR expression RPAREN'
    if '&' in p[2]:
        p[0] = '(' + p[4] + '|' + p[2] + ')'
    else:
        p[0] = '(' + p[2] + '|' + p[4] + ')'

def p_expression_imply(p):
    'expression : LPAREN expression IMPLY expression RPAREN'
    p[0] = '((~' + p[2] + ')|' + p[4] + ')'

def p_expression_and_or(p):
    '''expression : LPAREN LPAREN expression AND expression RPAREN OR expression RPAREN'''
    p[0] = '((' + p[3] + '|' + p[5] + ')&(' + p[3] + '|' + p[8] +'))'

def p_expression_or_and(p):
    'expression : LPAREN expression OR LPAREN expression AND expression RPAREN RPAREN'
    p[0] = '((' + p[2] + '|' + p[5] + ')&(' + p[2] + '|' + p[7] + '))'

def p_expression_not(p):
    'expression : LPAREN NOT PREDIC RPAREN'
    p[0] = '(~' + p[3] + ')'

def p_expression_not_and(p):
    'expression : LPAREN NOT LPAREN expression AND expression RPAREN RPAREN'
    p[0] = '((~' + p[4] + ')|(~' + p[6] + '))'

def p_expression_not_or(p):
    'expression : LPAREN NOT LPAREN expression OR expression RPAREN RPAREN'
    p[0] = '((~' + p[4] + ')&(~' + p[6] + '))'

def p_expressioin_not_not(p):
    'expression : LPAREN NOT LPAREN NOT PREDIC RPAREN RPAREN'
    p[0] = p[5]

def p_expression_predic(p):
    'expression : PREDIC'
    p[0] = p[1]

lelxer = lex.lex()
parser = yacc.yacc()

def lexParse(data):
    lelxer.input(data)
    lists = []
    sublist = []
    while True:
        tok = lelxer.token()
        if tok is None:
            break
        if tok.type == 'PREDIC':
            sublist.append(tok.value)
        elif tok.type == 'NOT':
            tok = lelxer.token()
            sublist.append('~' + tok.value)
        elif tok.type == 'AND':
            lists.append(sublist)
            sublist = []
    if len(sublist) > 0:
        lists.append(sublist)
    return lists

def parseSentence(data):
    lists = []
    while True :
        result = parser.parse(data)
        if result == data:
            lists = lexParse(result)
            break
        data = result
    return lists

global varible
varible = 'a'

def getUniqueVar():
    global varible
    ans = varible
    varible = chr(ord(varible) + 1)
    return ans

class FOLResolution:

    def run(self):
        self.buildTable()
        
        self.results = []
        for query in self.querys:
            table = copy.deepcopy(self.indexTable)
            kb = copy.deepcopy(self.myKBS)
            query.setOpposite()
            kb.append([query])
            item = table.get(query.getName())
            if item is None:
                self.results.append(False) # ???
                continue
            item[query.negative()].append([len(kb) - 1,0])
            self.results.append(self.resolute2(table, kb))
     
    def resolute2(self, table, kb):
        self.forbidDict = {}
        index = len(kb) - 1
        while index < len(kb):
            clause = kb[index]
            for col in range(0, len(clause)):
                item = table.get(clause[col].getName())
                oPreds = item[1 - clause[col].negative()]
                for opred in oPreds:
                    if opred[0] >= index:
                        continue
                    
                    if self.extendCheck(kb, index, col) == False or self.extendCheck(kb, opred[0], opred[1]) == False:
                        continue
                    newPred = self.unify(clause, col, kb[opred[0]], opred[1])
                    if newPred is None:
                        continue
                    if len(newPred) == 0:
                        return True
                    else:
                        newPred = self.simpleFactoring(newPred)
                        if self.existCheck2(table, kb, newPred):
                            continue
                        #test
                        #for literal in newPred:
                        #    print literal.getName(), literal.negative(), literal.getParaters(),
                        #print ""
                        
                        global MAXKB
                        #print len(kb)
                        if len(kb) > MAXKB:
                            return True
                        kb.append(newPred)
                        for k in range(0, len(newPred)):
                            newClause = newPred[k]
                            item = table.get(newClause.getName())
                            item[newClause.negative()].append([len(kb) - 1, k])
            index = index + 1
        return False

    def simpleFactoring(self, sentence):
        dupDict = {}
        for i in range(0, len(sentence)):
            for j in range(i + 1, len(sentence)):
                if sentence[i].getName() == sentence[j].getName() and sentence[i].negative() == sentence[j].negative() and sentence[i].getParaters() == sentence[j].getParaters():
                    dupDict[i] = True
                    break
        if len(dupDict) == 0:
            return sentence
        else:
            newSen = []
            for i in range(0, len(sentence)):
                if dupDict.has_key(i):
                    continue
                newSen.append(sentence[i])
            return newSen



    # only work for uniclause with const varible
    def existCheck(self, table, kb, sentence):
        fpred = sentence[0]
        item = table.get(fpred.getName())
        if item is None:
            return True
        elist = item[fpred.negative()]
        for pos in elist:
            row = pos[0]
            col = pos[1]
            if len(kb[row]) != len(sentence):
                continue
            if fpred.getParaters() == kb[row][col].getParaters():
                return False
            else:
                return True
    
    # very strict, but extremely slow
    def existCheck2(self, table, kb, sentence):
        if self.alwaysTrueCheck(sentence):
            return True

        nameDict = {}
        rowDict = {}
        for literal in sentence:
            if nameDict.has_key(literal.getName()):
                continue
            nameDict[literal.getName()] = True
            nameList = table.get(literal.getName())
            if nameList is None:
                return False
            equalList = nameList[literal.negative()]
            for esen in equalList:
                if rowDict.has_key(esen[0]):
                    continue
                else:
                    rowDict[esen[0]] = True
                paraDict = {}
                if self.sentenceEqual(sentence, kb[esen[0]], paraDict):
                    return True
        return False

    def sentenceEqual(self, sen1, sen2, paraDict):
        if len(sen1) == 0 and len(sen2) == 0:
            return True
        if len(sen1) != len(sen2):
            return False
        for i in range(0, len(sen1)):
            for j in range(0, len(sen2)):
                if sen1[i].getName() == sen2[j].getName() and sen1[i].negative() == sen2[j].negative():
                    curDict = copy.deepcopy(paraDict)
                    if self.unifyVarible(sen1, i, sen2, j, curDict):
                        return True
        return False

    def unifyVarible(self, sen1, col1, sen2, col2, paraDict):
        para1 = sen1[col1].getParaters()
        para2 = sen2[col2].getParaters()
        for i in range(0, len(para1)):
            var1 = self.isVarible(para1[i])
            var2 = self.isVarible(para2[i])
            if var1 and var2:
                if paraDict.has_key(para2[i]):
                    if paraDict[para2[i]] != para1[i]:
                        return False
                else:
                    paraDict[para2[i]] = para1[i]
            elif var1 == False and var2 == False:
                if para1[i] != para2[i]:
                    return False
            else:
                return False
        newSen1 = []
        for i in range(0, len(sen1)):
            if i == col1:
                continue
            newSen1.append(sen1[i])
        sen1 = newSen1

        newSen2 = []
        for i in range(0, len(sen2)):
            if i == col2:
                continue
            newSen2.append(sen2[i])
        sen2 = newSen2
        return self.sentenceEqual(sen1, sen2, paraDict)

    def alwaysTrueCheck(self, sentence):
        for i in range(0, len(sentence)):
            for j in range(i + 1, len(sentence)):
                literal1 = sentence[i]
                literal2 = sentence[j]
                if literal1.getName() == literal2.getName() and literal1.negative() != literal2.negative():
                    para1 = literal1.getParaters()
                    para2 = literal2.getParaters()
                    isMatch = True
                    for k in range(0, len(para1)):
                        if para1[k] !=para2[k]:
                            isMatch = False
                            break
                    if isMatch:
                        return True
        return False


    def isVarible(self, rhs):
        if len(rhs) == 1 and ord(rhs) >= ord('a') and ord(rhs) <= ord('z'):
            return True
        else:
            return False

    def standarVar(self, lhs, rhs):
        lparaDict = {}
        for clause in lhs:
            paras = clause.getParaters()
            for para in paras:
                if self.isVarible(para):
                    lparaDict[para] = para
        rparaDict = {}
        rusedDict = {}
        for clause in rhs:
            paras = clause.getParaters()
            newParas = []
            for para in paras:
                if self.isVarible(para):
                    if lparaDict.has_key(para):
                        if rparaDict.has_key(para) == False:
                            newVar = 'a'
                            while lparaDict.has_key(newVar) or rusedDict.has_key(newVar):
                                newVar = chr(ord(newVar) + 1)
                            rparaDict[para] = newVar
                            lparaDict[newVar] = newVar
                            rusedDict[newVar] = newVar
                            newParas.append(newVar)
                        else:
                            newParas.append(rparaDict[para])
                    else:
                        newParas.append(para)
                        rusedDict[para] = para
                else:
                    newParas.append(para)
            clause.setParaters(newParas)


    def unify(self, lhs, lcol, rhs, rcol):

        self.standarVar(lhs, rhs)

        clauKB = lhs[lcol]
        clauQ = rhs[rcol]
        paraKB = clauKB.getParaters()
        paraQ = clauQ.getParaters()
        parDict = {}
        newPreds = []
        for i in range(0, len(paraKB)):
            varKB = paraKB[i]
            varQ = paraQ[i]
            kbFlag = self.isVarible(varKB)
            qFlag = self.isVarible(varQ)
            if kbFlag == True and qFlag == False:
                item = parDict.get(varKB)
                if item is None:
                    parDict[varKB] = varQ
                elif parDict[varKB] != varQ:
                    return None
            elif kbFlag == False and qFlag == False:
                if varKB != varQ:
                    return None
            elif kbFlag == False and qFlag == True:
                item = parDict.get(varQ)
                if item is None:
                    parDict[varQ] = varKB
                elif parDict[varQ] != varKB:
                    return None
            else:
                itemKB = parDict.get(varKB)
                itemQ = parDict.get(varQ)
                if itemKB is None and itemQ is None:
                    parDict[varQ] = varKB
                elif itemKB is not None and itemQ is None:
                    parDict[varQ] = parDict[varKB]
                elif itemKB is None and itemQ is not None:
                    #parDict[varKB] = parDict[itemQ]
                    parDict[varKB] = itemQ
                else:
                    #parDict[itemQ] = parDict[itemKB]
                    parDict[varQ] = itemKB
        for i in range(0, len(lhs)):
            if i == lcol:
                continue
            paras = lhs[i].getParaters()
            newPred = copy.deepcopy(lhs[i])
            newParas = []
            for para in paras:
                if self.isVarible(para):
                    item = parDict.get(para)
                    if item is None:
                        newParas.append(para)
                    else:
                        newParas.append(item)
                else:
                    newParas.append(para)
            newPred.setParaters(newParas)
            newPreds.append(newPred)
        for i in range(0, len(rhs)):
            if i == rcol:
                continue
            paras = rhs[i].getParaters()
            newPred = copy.deepcopy(rhs[i])
            newParas = []
            for para in paras:
                if self.isVarible(para):
                    item = parDict.get(para)
                    if item is None:
                        newParas.append(para)
                    elif self.isVarible(item) and parDict.has_key(item):
                        newParas.append(parDict[item])
                    else:
                        newParas.append(item)
                else:
                    newParas.append(para)
            newPred.setParaters(newParas)
            newPreds.append(newPred)
        #return newPreds
        if self.maxLenCheck(newPreds):
            return newPreds
        else:
            return None

    def extendCheck(self, kb, row, col):
        clause = kb[row]
        for literal in clause:
            if literal.getName() == clause[col].getName() and literal.negative() != clause[col].negative():
            #if literal.getName() == clause[col].getName():
                item = self.forbidDict.get(row)
                if item is not None:
                    for i in item:
                        if i == col:
                            return False
                    item.append(col)
                else:
                    self.forbidDict[row] = [col]
                    break
        return True

    def extendCheck2(self, pre, cur):
        return True
        item = self.forbidDict.get(cur)
        if item is None:
            return True # should not happen
        else:
            for line in item:
                if pre == line:
                    return False
        return True

    def maxLenCheck(self, clauses):
        #return True
        if len(clauses) > self.maxLen + 2:
        #if len(clauses) > 3:
            return False
        else:
            return True

    def loadFile(self):
        f = open(inFile)
        self.queryNum = (int)(f.readline().rstrip('\n'))
        self.querys = []
        for i in range(0, self.queryNum):
            sentence = f.readline().rstrip('\n')
            sentence = sentence.replace(' ', '')
            queryStr = lexParse(sentence)
            query = Predicate()
            query.build(queryStr[0][0])
            self.querys.append(query)
        
        self.kbNum = (int)(f.readline().rstrip('\n'))
        self.myKBS = []
        self.maxLen = 1
        for i in range(0, self.kbNum):
            sentence = f.readline().rstrip('\n')
            sentence = sentence.replace(' ', '')
            subkb = parseSentence(sentence)
            self.insertList(subkb)
        f.close()
        return

    def writeFile(self):
        f = open(outFile, 'w')
        for ans in self.results:
            f.write(str(ans).upper() + '\n')
        f.close()
        return

    def insertList(self, sentences):
        for sentence in sentences:
            sublist = []
            for clauseStr in sentence:
                predicate = Predicate()
                predicate.build(clauseStr)
                sublist.append(predicate)
            if self.maxLen < len(sublist):
                self.maxLen = len(sublist)
            self.myKBS.append(sublist)

    def buildTable(self):
        self.indexTable = {}
        for i in range(0, len(self.myKBS)):
            sentence = self.myKBS[i]
            for j in range(0, len(sentence)):
                clause = sentence[j]
                item = self.indexTable.get(clause.getName())
                if item is None:
                    item = [[], []]
                    self.indexTable[clause.getName()] = item
                item[clause.negative()].append([i, j])


class Predicate:
    def build(self, predic):
        lelxer.input(predic)
        tok = lelxer.token()
        self.paraters = []
        if tok.type == 'NOT':
            self.neg = 0;
            tok = lelxer.token()
            self.predicate = tok.value
        elif tok.type == 'PREDIC':
            self.predicate = tok.value
            self.neg = 1;
        lParent = self.predicate.find('(')
        paraStr = self.predicate[lParent + 1: len(self.predicate) - 1]
        self.predicate = self.predicate[:lParent]
        lelxer.input(paraStr)
        while True:
            tok = lelxer.token()
            if not tok:
                break
            if tok.type == 'CONST':
                self.paraters.append(tok.value)
            elif tok.type == 'VAR':
                self.paraters.append(tok.value)
 
    def getName(self):
        return self.predicate

    def getParaters(self):
        return self.paraters

    def setParaters(self, paras):
        self.paraters = paras

    def negative(self):
        return self.neg
    
    def setOpposite(self):
        self.neg = 1 - self.neg

    def match(self, rhs):
        return self.predicate == rhs.predicate and self.neg != rhs.neg and self.paraters == rhs.paraters
    
#main

if __name__ == '__main__':
    resolution = FOLResolution()
    resolution.loadFile()
    resolution.run()
    resolution.writeFile()
    
    
