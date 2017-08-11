import java.awt.*;
import static java.awt.Color.*;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.geom.AffineTransform;
import java.awt.geom.Ellipse2D;
import java.awt.geom.GeneralPath;
import java.awt.geom.RoundRectangle2D;
import java.util.Random;
import javax.swing.BorderFactory;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;

public class WumpusWorld extends JFrame {
    
    private final int xdim;
    private final int ydim;
    
    private int agent_x;
    private int agent_y;
    private boolean agent_alive;
    
    private int wumpus_x;
    private int wumpus_y;
    private boolean wumpus_alive;

    private boolean has_gold;
    private boolean has_arrow;
    
    private boolean[][] pit;
    private boolean[][] gold;
    
    private final WPanel wp;
    
    public WumpusWorld(int xdim, int ydim) {
	
        super("Wumpus");
        
	this.xdim = xdim;
	this.ydim = ydim;
        
	agent_x = 0;
	agent_y = 0;
	agent_alive = true;
	
        wumpus_x = xdim-1;
	wumpus_y = ydim-1;
	wumpus_alive = true;
	
        has_gold = false;
        has_arrow = true;
	
        pit = new boolean[xdim][ydim];
        gold = new boolean[xdim][ydim];
      
	super.setResizable(false);
	wp = new WPanel(this);
	super.add(wp);
        super.pack();
	super.setVisible(true);
        
    }

    public int getXDim() {
	return xdim;
    }

    public int getYDim() {
	return ydim;
    }
    
    public void setPit(int x, int y, boolean value) {
        if (x>=0 && x<xdim && y>=0 && y<ydim)
            pit[x][y] = value;
    }

    public boolean getPit(int x, int y) {
        if (x>=0 && x<xdim && y>=0 && y<ydim)
            return pit[x][y];
        else
            return false;
    }
    
    public void setGold(int x, int y, boolean value) {
        if (x>=0 && x<xdim && y>=0 && y<ydim)
            gold[x][y] = value;
    }

    public boolean getGold(int x, int y) {
        if (x>=0 && x<xdim && y>=0 && y<ydim)
            return gold[x][y];
        else
            return false;
    }

    public void setAgentPos(int x, int y) {
	agent_x = x;
	agent_y = y;
    }

    public int getAgentPosX() {
	return agent_x;
    }

    public int getAgentPosY() {
	return agent_y;
    }

    public void setWumpusPos(int x, int y) {
	wumpus_x = x;
	wumpus_y = y;
    }

    public int getWumpusPosX() {
	return wumpus_x;
    }

    public int getWumpusPosY() {
	return wumpus_y;
    }
    
    public boolean isWumpus(int x, int y) {
        return (wumpus_x == x && wumpus_y == y);
    }

    public boolean agentAlive() {
	return agent_alive;
    }

    public boolean wumpusAlive() {
	return wumpus_alive;
    }
    
    public boolean hasGold() {
	return has_gold;
    }
    
    public boolean hasArrow() {
	return has_arrow;
    }

    public void randomize(int goldPieces, float pitProbability) {
        Random random = new Random();
        randomize(random, goldPieces, pitProbability);        
    }
    
    public void randomize(long seed, int goldPieces, float pitProbability) {
        Random random = new Random(seed);
        randomize(random, goldPieces, pitProbability);
    }
    
    private void randomize(Random random, int goldPieces, float pitProbability) {
	
        // wumpus
        int xw;
        int yw;
        do {
            xw = random.nextInt(xdim);
            yw = random.nextInt(ydim);
        } while (xw == agent_x && yw == agent_y);
        wumpus_x = xw;
        wumpus_y = yw;
        
        // gold
        gold = new boolean[xdim][ydim]; // reset
        for (int i=0; i<Math.min(goldPieces,xdim*ydim); i++) {
            int x;
            int y;
            do {
                x = random.nextInt(xdim);
                y = random.nextInt(ydim);
            } while (gold[x][y]);
            gold[x][y] = true;
        }
        
        // pits
        pit = new boolean[xdim][ydim]; // reset
	for (int i=0; i<xdim; i++) {
	    for (int j=0; j<ydim; j++) {
                if (i != wumpus_x && j != wumpus_y && !gold[i][j]
                        && i != agent_x && j != agent_y 
                        && random.nextFloat() <= pitProbability)
                    pit[i][j] = true;
            }
        }
        
        repaint();
	
    }
    
    public void moveAgent(String dir) {
	switch (dir) {
	    case "north":
		agent_y += 1;
		break;
	    case "east":
		agent_x += 1;
		break;
	    case "south":
		agent_y -= 1;
		break;
	    case "west":
		agent_x -= 1;
		break;
            default:
                break;
	}
	agent_x = Math.max(0,agent_x);
	agent_y = Math.max(0,agent_y);
	agent_x = Math.min(agent_x,xdim-1);
	agent_y = Math.min(agent_y,ydim-1);
        if (pit[agent_x][agent_y] ||
                wumpus_x == agent_x && wumpus_y == agent_y)
            agent_alive = false;
        repaint();
    }

    public void grabGold() {
	if (gold[agent_x][agent_y]) {
	    has_gold = true;
            gold[agent_x][agent_y] = false;
        }   
        repaint();
    }
    
    public boolean shoot(String dir) {
        boolean result = false;
        switch (dir) {
            case "north":
                if (agent_x == wumpus_x && agent_y < wumpus_y 
                        && wumpus_alive && has_arrow)
                    result = true;
                break;
            case "west":
                if (agent_x > wumpus_x && agent_y == wumpus_y 
                        && wumpus_alive && has_arrow)
                    result = true;
                break;
            case "south":
                if (agent_x == wumpus_x && agent_y > wumpus_y 
                        && wumpus_alive && has_arrow)
                    result = true;
                break;
            case "east":
                if (agent_x < wumpus_x && agent_y == wumpus_y 
                        && wumpus_alive && has_arrow)
                    result = true;
                break;
            default:
                break;
        }
        if (result)
            wumpus_alive = false;
        has_arrow = false;
        repaint();
        return result;
    }
    
    public boolean stench() {
        return (agent_x == wumpus_x && agent_y == wumpus_y-1 ||
                agent_x == wumpus_x && agent_y == wumpus_y+1 ||
                agent_x == wumpus_x-1 && agent_y == wumpus_y ||
                agent_x == wumpus_x+1 && agent_y == wumpus_y);
    }
    
    public boolean breeze() {
        return (agent_y > 0 && pit[agent_x][agent_y-1] ||
                agent_x > 0 && pit[agent_x-1][agent_y] ||
                agent_y < ydim-1 && pit[agent_x][agent_y+1] ||
                agent_x < xdim-1 && pit[agent_x+1][agent_y]);
    }    
    
    public boolean glitter() {
        return (gold[agent_x][agent_y]);
    }
    
    class WPanel extends JPanel {
	
	WumpusWorld wumpusWorld;
	
        public WPanel(WumpusWorld wumpusWorld) {
	    this.wumpusWorld = wumpusWorld;            
            super.setPreferredSize(new Dimension(500, 500));
        }

        @Override
        public void paintComponent(Graphics g) {
            super.paintComponent(g);
            
            int gridCellSize = Math.min(
                    (int) this.getSize().getWidth() / xdim,
                    (int) this.getSize().getHeight() / ydim);
            int cellMargin = gridCellSize / 10;

	    // grid
	    for (int i=0; i<xdim+1; i++)
		g.drawLine(i*gridCellSize,0,i*gridCellSize,ydim*gridCellSize);
	    for (int i=0; i<wumpusWorld.getYDim()+1; i++)
		g.drawLine(0,i*gridCellSize,xdim*gridCellSize,i*gridCellSize);

	    // pits
	    for (int i=0; i<xdim; i++)
		for (int j=0; j<ydim; j++) {
                    int k = ydim - j - 1;
                    if (pit[i][j])
                        g.fillRoundRect(i*gridCellSize+cellMargin,
                                k*gridCellSize+cellMargin,
				gridCellSize-2*cellMargin,
				gridCellSize-2*cellMargin,
				2*cellMargin,2*cellMargin);
		}

	    // gold
	    for (int i=0; i<xdim; i++)
		for (int j=0; j<ydim; j++) {
                    int k = ydim - j - 1;
                    if (gold[i][j]) {
                        g.drawString("G",
                                i*gridCellSize+33,
                                k*gridCellSize+20);
                    }
		}
            
            if (agent_alive)
                paintAgent((Graphics2D) g,
                        agent_x*gridCellSize+cellMargin,
                        (ydim-agent_y-1)*gridCellSize+cellMargin,
                        gridCellSize-2*cellMargin,
                        gridCellSize-2*cellMargin);
            
            if (wumpus_alive)
                paintWumpus((Graphics2D) g,
                        wumpus_x*gridCellSize+cellMargin,
                        (ydim-wumpus_y-1)*gridCellSize+cellMargin,
                        gridCellSize-2*cellMargin,
                        gridCellSize-2*cellMargin);
   
        }

        
        
        
        
        /**
     * Paints the transcoded SVG image on the specified graphics context. You
     * can install a custom transformation on the graphics context to scale the
     * image.
     * 
     * @param g Graphics context.
     */
    private void paintWumpus(Graphics2D g, int x, int y, int width, int height) {
        Shape shape;
        
        int origX = 4;
        int origY = 10;
        int origWidth = 56;
        int origHeight = 44;
    
        double scale = Math.min(
                (double) width / (double) origWidth,
                (double) height / (double) origHeight);
        
        AffineTransform oldTransform = g.getTransform();
        AffineTransform newTransform = new AffineTransform(g.getTransform());
        newTransform.translate(x,y);
        newTransform.scale(scale, scale);
        g.setTransform(newTransform);

        
        float origAlpha = 1.0f;
        Composite origComposite = g.getComposite();
        if (origComposite instanceof AlphaComposite) {
            AlphaComposite origAlphaComposite = (AlphaComposite)origComposite;
            if (origAlphaComposite.getRule() == AlphaComposite.SRC_OVER) {
                origAlpha = origAlphaComposite.getAlpha();
            }
        }
        
        java.util.LinkedList<AffineTransform> transformations = new java.util.LinkedList<>();
        

        // 

        // _0
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, 4.149475E-6f, -698.0315f));

        // _0_0

        // _0_0_0
        //   
        g.setPaint(WHITE);
        shape = new GeneralPath();

        g.fill(shape);
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -40.449078f, -97.84824f));

        // _0_0_1
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_0
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(44.29584, 116.51162);
        ((GeneralPath) shape).lineTo(45.98101, 110.97464);
        ((GeneralPath) shape).lineTo(52.240204, 120.60417);
        ((GeneralPath) shape).lineTo(59.221615, 123.25229);
        ((GeneralPath) shape).lineTo(60.184566, 114.10423);
        ((GeneralPath) shape).lineTo(64.99933, 107.6043);
        ((GeneralPath) shape).lineTo(81.851006, 108.32652);
        ((GeneralPath) shape).lineTo(85.221344, 113.14128);
        ((GeneralPath) shape).lineTo(83.77692, 123.9745);
        ((GeneralPath) shape).lineTo(90.99907, 118.196785);
        ((GeneralPath) shape).lineTo(90.03612, 112.90054);
        ((GeneralPath) shape).lineTo(98.22122, 123.01155);
        ((GeneralPath) shape).lineTo(85.702835, 129.99297);
        ((GeneralPath) shape).lineTo(83.05471, 142.02988);
        ((GeneralPath) shape).lineTo(80.64732, 145.40022);
        ((GeneralPath) shape).lineTo(90.03612, 145.40022);
        ((GeneralPath) shape).lineTo(90.03612, 149.49277);
        ((GeneralPath) shape).lineTo(74.14739, 150.21498);
        ((GeneralPath) shape).lineTo(76.073296, 146.12244);
        ((GeneralPath) shape).lineTo(64.7586, 145.40022);
        ((GeneralPath) shape).lineTo(66.44376, 149.73352);
        ((GeneralPath) shape).lineTo(49.832825, 149.97426);
        ((GeneralPath) shape).lineTo(53.20316, 145.88171);
        ((GeneralPath) shape).lineTo(61.869736, 144.67801);
        ((GeneralPath) shape).lineTo(58.4994, 128.30782);
        ((GeneralPath) shape).lineTo(47.906918, 123.974525);
        ((GeneralPath) shape).closePath();

        g.setPaint(BLACK);
        g.setStroke(new BasicStroke(1, 0, 0, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_0
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_1
        shape = new Ellipse2D.Double(67.10930633544922, 119.59864044189453, 3.1167361736297607, 2.9841091632843018);
        g.setPaint(WHITE);
        g.fill(shape);
        g.setPaint(BLACK);
        g.setStroke(new BasicStroke(0.9992126f, 0, 1, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_1
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_2
        shape = new Ellipse2D.Double(74.93429565429688, 119.93021392822266, 3.5809309482574463, 3.3156769275665283);
        g.setPaint(WHITE);
        g.fill(shape);
        g.setPaint(BLACK);
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_2
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_3
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(64.191505, 117.01242);
        ((GeneralPath) shape).curveTo(69.695526, 115.221954, 69.76184, 115.221954, 69.76184, 115.221954);

        g.setStroke(new BasicStroke(1, 0, 0, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_3
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_4
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(75.33218, 115.28827);
        ((GeneralPath) shape).curveTo(80.50463, 116.87979, 80.50463, 116.87979, 80.50463, 116.87979);

        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_4
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_5
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(63.39574, 127.2247);
        ((GeneralPath) shape).lineTo(68.70082, 129.28043);
        ((GeneralPath) shape).lineTo(76.9237, 130.00987);
        ((GeneralPath) shape).lineTo(81.36671, 128.08678);

        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_5
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_6
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(66.97667, 129.01517);
        ((GeneralPath) shape).lineTo(67.50718, 132.66241);
        ((GeneralPath) shape).lineTo(69.76184, 132.66241);
        ((GeneralPath) shape).lineTo(70.09341, 129.6783);
        ((GeneralPath) shape).lineTo(70.0271, 129.6783);

        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_6
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_1_7
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(73.87328, 130.1425);
        ((GeneralPath) shape).lineTo(74.20485, 133.45818);
        ((GeneralPath) shape).lineTo(76.45951, 133.52448);
        ((GeneralPath) shape).lineTo(76.72477, 130.14249);

        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_1_7

        g.setTransform(transformations.pop()); // _0_0_1

        g.setTransform(transformations.pop()); // _0_0
                
        g.setTransform(oldTransform); // my additional

    }
/**
     * Paints the transcoded SVG image on the specified graphics context. You
     * can install a custom transformation on the graphics context to scale the
     * image.
     * 
     * @param g Graphics context.
     */
    private void paintAgent(Graphics2D g, int x, int y, int width, int height) {
        
        int origX = 1;
        int origY = 0;
        int origWidth = 36;
        int origHeight = 55;
    
        double scale = Math.min(
                (double) width / (double) origWidth,
                (double) height / (double) origHeight);
        
        AffineTransform oldTransform = g.getTransform();
        AffineTransform newTransform = new AffineTransform(g.getTransform());
        newTransform.translate(x,y);
        newTransform.scale(scale, scale);
        g.setTransform(newTransform);
        
        Shape shape;
        
        float origAlpha = 1.0f;
        Composite origComposite = g.getComposite();
        if (origComposite instanceof AlphaComposite) {
            AlphaComposite origAlphaComposite = (AlphaComposite)origComposite;
            if (origAlphaComposite.getRule() == AlphaComposite.SRC_OVER) {
                origAlpha = origAlphaComposite.getAlpha();
            }
        }
        
        java.util.LinkedList<AffineTransform> transformations = 
                new java.util.LinkedList<>();
       
        // 
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1.0666667f, 0, 0, 1.0666667f, 0, 2.0345053E-6f));

        // _0
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -3.211553f, -1.164079f));

        // _0_0
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -60.06797f, -944.3989f));

        // _0_0_0
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_0_0
        shape = new Ellipse2D.Double(63.7795295715332, 248.031494140625, 14.17322826385498, 14.17322826385498);
        g.setPaint(BLACK);
        g.setStroke(new BasicStroke(1, 0, 0, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_0_0
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_0_1
        shape = new RoundRectangle2D.Double(63.77952575683594, 262.2047119140625, 14.17322826385498, 21.259841918945312, 3.7955775260925293, 3.7955775260925293);
        g.setStroke(new BasicStroke(0.9992126f, 0, 1, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_0_1
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(0.9992655f, 0.0383204f, -0.0383204f, 0.9992655f, 0, 0));

        // _0_0_0_2
        shape = new RoundRectangle2D.Double(102.29635620117188, 978.3855590820312, 5.777796745300293, 14.304100036621094, 3.7955775260925293, 3.7955775260925293);
        g.setStroke(new BasicStroke(1, 0, 1, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_0_2

        // _0_0_0_3
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(82.62695, 967.65);
        ((GeneralPath) shape).lineTo(96.345215, 967.65);

        g.setStroke(new BasicStroke(0.983819f, 0, 0, 4));
        g.draw(shape);

        // _0_0_0_4
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(82.159966, 953.4768);
        ((GeneralPath) shape).curveTo(87.58694, 961.39764, 95.72998, 968.5538, 82.159966, 981.82324);

        g.setStroke(new BasicStroke(1, 0, 0, 4));
        g.draw(shape);

        // _0_0_0_5
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(82.159966, 981.82324);
        ((GeneralPath) shape).curveTo(82.159966, 953.4768, 82.159966, 953.4768, 82.159966, 953.4768);
        ((GeneralPath) shape).lineTo(82.159966, 953.4768);

        g.setStroke(new BasicStroke(1, 1, 0, 4));
        g.draw(shape);

        // _0_0_0_6
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(95.08768, 970.64703);
        ((GeneralPath) shape).lineTo(96.31303, 967.5801);
        ((GeneralPath) shape).lineTo(95.04727, 964.78705);

        g.setStroke(new BasicStroke(1, 0, 0, 4));
        g.draw(shape);

        // _0_0_0_7
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(70.74171, 963.32446);
        ((GeneralPath) shape).curveTo(82.12844, 968.0362, 82.12844, 968.1016, 82.12844, 968.1016);

        g.setStroke(new BasicStroke(0.9992126f, 1, 1, 4));
        g.draw(shape);
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(0.9993884f, -0.03496941f, 0.03496941f, 0.9993884f, 0, 0));

        // _0_0_0_8
        shape = new RoundRectangle2D.Double(37.28730773925781, 983.639892578125, 5.777796745300293, 14.304100036621094, 3.7955775260925293, 3.7955775260925293);
        g.setStroke(new BasicStroke(1, 0, 1, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_0_8
        transformations.push(g.getTransform());
        g.transform(new AffineTransform(1, 0, 0, 1, -4.149475E-6f, 698.0315f));

        // _0_0_0_9
        shape = new GeneralPath();
        ((GeneralPath) shape).moveTo(78.20199, 265.55475);
        ((GeneralPath) shape).curveTo(89.45784, 271.90253, 89.65416, 271.90253, 89.65416, 271.90253);

        g.setStroke(new BasicStroke(1, 0, 0, 4));
        g.draw(shape);

        g.setTransform(transformations.pop()); // _0_0_0_9

        g.setTransform(transformations.pop()); // _0_0_0

        g.setTransform(transformations.pop()); // _0_0

        g.setTransform(transformations.pop()); // _0
        
        g.setTransform(oldTransform); // my additional

    }

            
        
        
    }       
        
    
}
