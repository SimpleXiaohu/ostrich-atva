package strsolver


class Example[A](op : => A) extends Thread{
  private var res : A = _
  var isDone = false
  override def run(): Unit = {
    try {
      println("thread" + getName + "begin")
      res = op
      isDone = true
      println("thread" + getName + "end" + ",res is " + res)
    }catch {
      case e : InterruptedException => {
        println("klllllllllllllllllllllll")
      }
    }
  }
  def getRes() : A = res
}