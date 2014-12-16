    package com.example.rbtreeproject
    
    //import com.example.rbtreeproject.CoqMain._
    import com.example.rbtreeproject.RBTree._
    import android.os.Bundle
    import android.app.Activity
    import android.view.Menu
    import android.graphics.Color;
    import android.graphics.Canvas;
    import android.graphics.Paint;
    import javax.microedition.khronos.opengles.GL10
    import javax.microedition.khronos.egl.EGLConfig
	import android.opengl.{GLSurfaceView, GLU} 
    import java.nio.{ByteOrder, ByteBuffer}
    import android.content.Context
    import android.view.Window
    
    class MWTApp extends Activity {
      var view: GLSurfaceView = null
      
       override def onPause() = {
		super.onPause()
		view.onPause()
		}
		 
		override def onResume() = {
		super.onResume()
		view.onResume()
		} 
      
    override def onCreate(savedInstanceState : Bundle) : Unit = {
    super.onCreate(savedInstanceState)
    requestWindowFeature(Window.FEATURE_NO_TITLE)
    setContentView(R.layout.activity_main)
    view = new GLSurfaceView(this)
    view.setEGLConfigChooser(8 , 8, 8, 8, 16, 0)
    view.setRenderer(new SimpleTriangleRender(this))
    // view.setRenderMode(GLSurfaceView.RENDERMODE_WHEN_DIRTY)
    view.setRenderMode(GLSurfaceView.RENDERMODE_CONTINUOUSLY)
 
this.setContentView(view) 
    /*val zero: Nat = O()
	val one: Nat = S(O())
	val two: Nat = S(S(O()))
	val three: Nat = S(S(S(O())))
	val red: Color = R()
	val empty: Tree = E()
	val a: Tree = T(red, empty, three, empty)
	val t1: Tree = rbinsert(1, empty)
	value(t1)	
	val b = toNat(4)
	val x = toInt(toNat(101))
	val t2: Tree = rbinsert(2, t1)
	traversal(t2)
	value(t2)
	val g = rbvalue(T(red, empty, one, empty))
	val c = color(t2)
	val c2 = rbcolor(t2)
    
    val bigTree: Tree = rbinsert(1,
	  rbinsert(2,
	    rbinsert(3,
	    rbinsert(4,
	    rbinsert(100,
	    rbinsert(12,
	    rbinsert(0, empty)))))))
	traversal(bigTree)
	rbtraversal(bigTree)
	member(three)(bigTree)
	rbmember(3, bigTree)
	rbmember(100, bigTree)
	rbmember(101, bigTree)
	rbtraversal(left(bigTree))
	rbtraversal(right(bigTree))*/
    
    }
    
    abstract class AbstractRenderer extends android.opengl.GLSurfaceView.Renderer {
def draw(gl:GL10)
 
def onDrawFrame(gl: GL10) = {
gl.glDisable(GL10.GL_DITHER)
gl.glClear(GL10.GL_COLOR_BUFFER_BIT | GL10.GL_DEPTH_BUFFER_BIT)
gl.glMatrixMode(GL10.GL_MODELVIEW)
gl.glLoadIdentity()
GLU.gluLookAt(gl, 0f, 0f, -5f, 0f, 0f, 0f, 0f, 1.0f, 0f)
gl.glEnableClientState(GL10.GL_VERTEX_ARRAY)
draw(gl)
}
 
def onSurfaceChanged(gl: GL10, width: Int, height: Int) = {
gl.glViewport(0,0,width,height)
val ratio:Float = width/height
gl.glMatrixMode(GL10.GL_PROJECTION)
gl.glLoadIdentity()
gl.glFrustumf(-ratio, ratio, -1, 1,3,7)
}
 
def onSurfaceCreated(gl: GL10, config: EGLConfig) = {
gl.glDisable(GL10.GL_DITHER)
gl.glHint(GL10.GL_PERSPECTIVE_CORRECTION_HINT, GL10.GL_FASTEST)
gl.glClearColor(0.5f, 0.5f, 0.5f, 1)
gl.glShadeModel(GL10.GL_SMOOTH)
gl.glEnable(GL10.GL_DEPTH_TEST)
}
}
 
class SimpleTriangleRender(context:Context) extends AbstractRenderer
{
private[this] val verts = 3
 
private[this] val vbb = ByteBuffer.allocateDirect(verts * 3 * 4)
vbb.order(ByteOrder.nativeOrder())
 
private[this] val ibb = ByteBuffer.allocateDirect(verts * 2)
ibb.order(ByteOrder.nativeOrder())
 
private[this] val vertBuffer = vbb.asFloatBuffer()
 
private[this] val indexBuffer = ibb.asShortBuffer()
 
private[this] val coords: Array[Float] = List(
-0.5f, -0.5f, 0.0f,
0.5f, -0.5f, 0.0f,
0.0f, 0.5f, 0.0f
).toArray
 
(0 until verts).foreach(i =>
(0 until 3).foreach(j => {
vertBuffer.put(coords(i*3+j))
})
)
 
private[this] val indexes = Array[Short](0, 1, 2)
(0 until 3).foreach(j => {
indexBuffer.put(indexes(j))
})
 
vertBuffer.position(0)
indexBuffer.position(0)
 
def draw(gl: GL10): Unit = {
gl.glColor4f(1.0f, 0f, 0f, 0.5f)
gl.glVertexPointer(3, GL10.GL_FLOAT, 0, vertBuffer)
gl.glDrawElements(GL10.GL_TRIANGLES, verts, GL10.GL_UNSIGNED_SHORT, indexBuffer)
}
} 
    
    override def onCreateOptionsMenu(menu : Menu) : Boolean = {
    getMenuInflater().inflate(R.menu.main, menu)
    return true
    }
    
    
    }

