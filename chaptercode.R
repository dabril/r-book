## Supporting R code for the book chapter
##
## Abril, D., Navarro-Arribas, G., Torra, V., Privacy Preserving Data Mining and
## Advanced Disclosure Risk with R.
##
## Note: this is just a list of R instructions and function definitions for
## the convenience of the reader. It is not a self contained R script.

# Install sdcMicro package
install.packages("sdcMicro", depend=TRUE)

# Load the sdcMicro package 
library(sdcMicro)

# Toy microdata table
mdata <- as.data.frame(rbind(c(15, 23, 42.01, 23, 50, 1150, 37) ,
                        c(12, 43, 59.93, 28, 70, 1960, 37) ,
                        c(64, 229, 319.27, 12, 84, 1008, 25) ,
                        c(12, 45, 62.07, 29, 73, 2117, 30) ,
                        c(28, 39, 74.21, 9, 30, 270, 40) ,
                        c(71, 102, 191.5, 10, 63, 630, 20) ,
                        c(23, 64, 95.16, 9, 74, 666, 10) ,
                        c(25, 102, 138.14, 72, 30, 2160, 80) ,
                        c(48, 230, 301.78, 26, 30, 780, 35) ,
                        c(32, 50, 90.62, 6, 45, 270, 15) ,
                        c(90, 200, 318.4, 8, 45, 360, 15) ,
                        c(16, 100, 125.56, 34, 55, 1870, 45) ))

# Additive Noise
p <- 0.2
mdata.noise.1 <- apply(mdata, 2, function(x) { x + rnorm(dim(mdata)[1], 0,
                                                         p * sd(x))})
#print(mdata.noise.1)

mdata.noise.2 <- addNoise(mdata, noise=0.2, method="additive")$xm
#print(mdata.noise.2)

# Microaggregation
mdata.microagg <- microaggregation(mdata, method="mdav", aggr=3)$mx
#print(mdata.microagg)

# Rank swapping
mdata.swap <- rankSwap(mdata,P=40,R0=0)
#print(mdata.swap)


# Install fpc package
install.packages("fpc", depend=TRUE)
library(fpc)

DistARI <- function(ari){
    return (1 - (1 + ari) / 2)
}

# Specific measures for information loss: cluster-based
ILRand <- function(original, masked) {
  ro <- kmeans(original, 3)
  rm <- kmeans(masked, 3)
  index <- cluster.stats(dist(original), ro[1]$cluster, rm[1]$cluster)
  randIndex <- index$corrected.rand
  return (DistARI(randIndex))
}

ILRandNoiseAddition <- function(original){
  function(nTimes){
    function(p){
      masked <- apply(original, 2, function(x){ x + rnorm(dim(original)[1], 0, p * sd(x))})
      min(replicate(10, ILRand(original, masked)))
    }
  }
}

# Compute the information for mdata
iLrand <- sapply((1:100) * 0.01, ILRandNoiseAddition(mdata)(10))

# Plot iLrand
plot(iLrand, ylim=c(0, 0.6), xlab="p*100")


############### Advanced techniques for disclosure risk evaluation
### EXAMPLE 1 ###
install.packages("lpSolveAPI", depend=TRUE)
library(lpSolveAPI)

original <- as.data.frame(rbind(c(1.00, 30.00, 27.00),
                                c(2.00, 50.00, 47.00),
                                c(3.00, 25.00, 31.00)))
protected <- as.data.frame(rbind(c(1.00, 20.00, 47.00),
                                 c(2.00, 20.00, 47.00),
                                 c(3.00, 23.00, 31.00)))

nrows <- nrow(original)
ncols <- ncol(original)

lpmo <- make.lp( nrow=(nrows * (nrows - 1) + 1), ncol=(ncols + nrows))

dataOs<-Normalization(original)
dataEs<-Normalization(protected)

index <- 0
#nRows <- nrow(dataOs)
#nCols <- ncol(dataOs)
data <- matrix(1,nrows^2, ncols + 1)
for (j in 1:nrows) {
  index<-((j - 1) * nrows)
  data[index + j, ncol(data)] <- 2
  
  d<-t(replicate(nrows, as.double(dataOs[j, 1:ncols])))
  data[(index + 1):((index + nrows)), 1:ncols] <- as.matrix(d - dataEs[,1:ncols])
}
data <- data^2

#PreComputed Constraints
constraints <- as.matrix(rbind(c( 1,  0.000000,  0.0000000),
                               c( 4,  2.309307, -1.6186147),
                               c( 1,  0.000000,  0.0000000),
                               c( 1, -2.927922,  4.9279220),
                               c( 4, -3.618615,  0.3093073),
                               c( 1, -3.618615,  0.3093073)))

#Constraints by columns
for(i in 1:(ncols)){
    set.column(lpmo, i, c(constraints[, i], 1))
}

inf <- 1
sup <- nrows - 1
for(i in (ncols + 1):(ncols + nrows)){
  set.column(lpmo, i, replicate((nrows - 1), 10), indices=inf:sup)
  inf <- inf + nrows - 1
  sup <- sup + nrows - 1 
}

#Objective
set.objfn(lpmo, c(replicate(ncols, 0),replicate(nrows, 1))) #Constraint types
#Constraint types
set.type(lpmo, (ncols + 1):(ncols + nrows), "binary")
#right-hand-side
set.constr.type(lpmo, c(replicate((nrows * (nrows - 1)), ">="), "="))
set.rhs(lpmo, c(replicate((nrows * (nrows - 1)), 0.0001), 1))
#print(lpmo)

solve(lpmo)
#print(get.objective(lpmo))
#print(get.variables(lpmo))


### EXAMPLE 2 ###

Normalization <- function(data) {
  ## Normalizes data
  dataN <- matrix(0, nrow(data), ncol(data))
  c<-sapply(data,sd)
  for (j in 1:(ncol(data))) {
      #Mean
      m<-mean(data[,j])
      for (i in 1:nrow(data)) {
        dataN[i,j]<-(data[i,j] - m)/c[j]			
      }
  }  
  return(dataN)
}

ProblemFormulation_LP <- function(data, nRows){

  #Num of variables
  numOfSubjects <- ncol(data) - 1
  #Num of Columns
  columnSE <- (numOfSubjects + 1)
  #Num of Y(r,t) Constraints
  nRc <- nRows * (nRows - 1)
  
  #1.Order the preferences (last column)
  orderVec <- sort(data[, columnSE], decreasing=TRUE, index.return=TRUE)
  dataOrd <- data[orderVec$ix, ]
  
  total <- matrix(0, 1, numOfSubjects)
  
  inf <- 1
  sup <- nRows - 1
  #2. Pair of elements of S, Sr > St
  for (i in 1:nRows) {
    elem <- which(dataOrd[, columnSE] < dataOrd[i, columnSE], arr.ind=TRUE)
    elem <- elem[inf:sup]
    if(length(elem) > 0) {
      repRow <- t(replicate(length(elem), dataOrd[i, 1:numOfSubjects]))
      #3. Subtraction of 2 vectors
      subPairs <- dataOrd[elem, 1:numOfSubjects] - repRow
      #4. Construct the matrix with all substractions
      total <- rbind(total, subPairs)
    }
    inf <- inf + nRows - 1
    sup <- sup + nRows - 1
  }
  total <- total[-1, ]
  
  #First, we create an LPMO with nRc +1 constraints and numOfSubjects+nRows
  #decision variables.
  lprec <- make.lp(nRc+1, numOfSubjects+nRows)
  
  #Constraints by columns
  for(i in 1:(numOfSubjects)){
    set.column(lprec, i, c(total[,i], 1)) 
  }
  
  #K
  inf<- 1
  sup<-nRows-1
  for(i in (numOfSubjects+1):(numOfSubjects+nRows)){
    set.column(lprec, i, replicate((nRows-1),10), indices=inf:sup)
    inf <- inf + nRows - 1
    sup <- sup + nRows - 1
  }
  
  set.constr.type(lprec, c(replicate(nRc, ">="), "="))
  set.rhs(lprec, c(replicate(nRc, 0.0001), 1))
  set.objfn(lprec, c(replicate(numOfSubjects,0),replicate(nRows, 1)))
  set.type(lprec, (numOfSubjects+1):(numOfSubjects+nRows), "binary")
                  
  return(lprec)
}

solveLP <- function(lprec){
  solve(lprec)
  #if returns a 0 value indicates that the model was successfully solved. 
  print("Objective")
  print(get.objective(lprec))
  print("Variables")
  print(get.variables(lprec))
  
  return(get.variables(lprec))
}

library(lpSolveAPI)

#columns {1, 2} - protection degree k = 2
mic1 <- microaggregation(mdata[, 1:2], method="mdav", aggr=2)
#columns {3, 4, 5} - protection degree k = 6
mic2 <- microaggregation(mdata[, 3:5], method="mdav", aggr=6)
#columns {6, 7} - protection degree k = 4
mic3 <- microaggregation(mdata[, 6:7], method="mdav", aggr=4)

mdata.microagg <- as.data.frame(cbind(mic1$mx, mic2$mx, mic3$mx))

nrows <- nrow(mdata)
ncols <- ncol(mdata.microagg)

dataOs <- Normalization(mdata)
dataEs <- Normalization(mdata.microagg)

index <- 0
#nRows <- nrow(dataOs)
#nCols <- ncol(dataOs)
data <- matrix(1,nrows^2, ncols + 1)
for (j in 1:nrows) {
  index<-((j - 1) * nrows)
  data[index + j, ncol(data)] <- 2
  
  d<-t(replicate(nrows, as.double(dataOs[j, 1:ncols])))
  data[(index + 1):((index + nrows)), 1:ncols] <- as.matrix(d - dataEs[,1:ncols])
}
data <- data^2

lprec <- ProblemFormulation_LP(data, nrows)
solWeights <- solveLP(lprec)

#Objective = 3 :=> 75% of re-identifications
#Weights :=> c(0.78227934, 0.16177286, 0.00000000, 0.00000000, 0.00000000, 0.01713346 0.03881434)
#K_i :=> c(0.00000000, 0.00000000, 0.00000000, 0.00000000, 0.00000000, 1.00000000, 0.00000000, 1.00000000, 0.00000000, 1.00000000, 0.00000000, 0.00000000)

